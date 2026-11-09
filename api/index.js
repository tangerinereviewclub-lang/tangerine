import { Redis } from "@upstash/redis";
import { gzipSync, gunzipSync } from "node:zlib";
import nodemailer from "nodemailer";
import { randomBytes, randomUUID, scryptSync, timingSafeEqual, createHash } from "node:crypto";

const redis = Redis.fromEnv({ automaticDeserialization: false });
const PIECES = ["users", "posts", "lists", "msgs", "clubs", "cmsgs", "meta"];
const META = ["reports", "pick", "suspended", "sessions", "resets", "fails"];
const pack = v => gzipSync(JSON.stringify(v)).toString("base64");
const unpack = s => JSON.parse(gunzipSync(Buffer.from(s, "base64")).toString());
async function load() {
  const raw = await redis.mget(...PIECES.map(k => "tg:" + k));
  const base = fresh(), db = {};
  PIECES.forEach((k, i) => {
    const v = raw[i] ? unpack(raw[i]) : null;
    if (k === "meta") META.forEach(m => { db[m] = v && v[m] !== undefined ? v[m] : base[m]; });
    else db[k] = v || base[k];
  });
  return { db, raw };
}
async function save(db, raw) {
  const now = {};
  PIECES.forEach((k, i) => {
    const v = k === "meta" ? Object.fromEntries(META.map(m => [m, db[m]])) : db[k];
    const p = pack(v);
    if (p !== raw[i]) { now["tg:" + k] = p; raw[i] = p; }
  });
  if (Object.keys(now).length) await redis.mset(now);
}

const TYPES = ["Movie","Documentary","Book","Game","Show","Anime","Music","Musical","Other"];
const TOPK = ["movies","albums","books","shows","games","other"];
const DAY = 864e5;
const ADMIN = (process.env.ADMIN_HANDLE || "").trim().toLowerCase().replace(/^@/, "");

class E extends Error {}
const bad = m => { throw new E(m); };
const sha = s => createHash("sha256").update(String(s)).digest("hex");
const id8 = () => randomUUID().replace(/-/g, "").slice(0, 10);
const clip = (s, n) => String(s == null ? "" : s).trim().slice(0, n);
const hashPw = pw => { const s = randomBytes(16).toString("hex"); return s + ":" + scryptSync(pw, s, 32).toString("hex"); };
const checkPw = (pw, h) => {
  if (!h) return false;
  const [s, x] = h.split(":");
  const a = scryptSync(String(pw || ""), s, 32), b = Buffer.from(x, "hex");
  return a.length === b.length && timingSafeEqual(a, b);
};
const emailOk = e => e.length <= 120 && /^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/.test(e);
const fresh = () => ({ users: [], posts: [], lists: [], msgs: [], clubs: [], cmsgs: [], reports: [], pick: null, suspended: [], sessions: {}, resets: {}, fails: {} });
const U = (db, id) => db.users.find(u => u.id === id);

function cleanTop(t) {
  const o = {};
  TOPK.forEach(k => { const a = Array.isArray(t && t[k]) ? t[k] : []; o[k] = [0, 1, 2, 3].map(i => clip(a[i], 60)); });
  return o;
}
function cleanIg(d) {
  let i = clip(d.insta, 100).replace(/^https?:\/\/(www\.)?instagram\.com\//i, "").replace(/^@/, "").replace(/[\/?].*$/, "");
  if (i && !/^[A-Za-z0-9._]{1,30}$/.test(i)) bad("Instagram name can only have letters, numbers, dots and underscores");
  const links = (Array.isArray(d.links) ? d.links : []).slice(0, 2).map(x => clip(x, 200)).map(x => (x && !/^https?:\/\//i.test(x) ? "https://" + x : x));
  links.forEach(x => { if (x) { try { new URL(x); } catch (e) { bad("One of your links is not valid"); } } });
  while (links.length < 2) links.push("");
  return { insta: i, igPrivate: !!d.igPrivate, links };
}
function cleanPost(d) {
  const type = clip(d.type, 20), media = clip(d.media, 80), title = clip(d.title, 100), text = clip(d.text, 10000);
  if (!TYPES.includes(type)) bad("Pick a media type");
  if (!media || !title || !text) bad("Add a media title, headline and review first");
  const r = parseInt(d.rating, 10);
  return { type, media, title, text, rating: r >= 1 && r <= 5 ? r : 0, spoiler: !!d.spoiler };
}
const pub = (u, viewer) => ({
  id: u.id, name: u.name, handle: u.handle, bio: u.bio, avatar: u.avatar, following: u.following, top: u.top,
  insta: viewer === u.id || !u.igPrivate ? u.insta : "", igPrivate: u.igPrivate, links: u.links, watch: u.watch
});
function blockedSet(db, uid) {
  const s = new Set();
  if (!uid) return s;
  db.users.forEach(u => { if (u.id === uid) u.blocked.forEach(x => s.add(x)); else if (u.blocked.includes(uid)) s.add(u.id); });
  return s;
}
function addPeople(db, c, uid, ids) {
  const bs = blockedSet(db, uid);
  (Array.isArray(ids) ? ids : []).slice(0, 60).forEach(x => {
    if (typeof x !== "string" || c.members.includes(x) || bs.has(x) || !U(db, x) || c.members.length >= 50) return;
    c.members.push(x);
  });
}
function clubMsgs(db, cid, uid) {
  const bs = blockedSet(db, uid);
  return db.cmsgs.filter(x => x.club === cid && !bs.has(x.by)).sort((a, b) => a.ts - b.ts).slice(-200);
}
function note(db, to, kind, from, pid) {
  const u = U(db, to);
  if (!u || to === from) return;
  u.notes.unshift({ id: id8(), kind, from, pid, ts: Date.now(), read: false });
  if (u.notes.length > 100) u.notes.length = 100;
}
function mentions(db, text, from, pid) {
  const seen = new Set();
  String(text).replace(/@([a-z0-9_]{3,20})/gi, (m, h) => {
    h = h.toLowerCase();
    if (seen.has(h)) return m;
    seen.add(h);
    const u = db.users.find(x => x.handle === h);
    if (u) note(db, u.id, "mention", from, pid);
    return m;
  });
}
function newSession(db, uid) {
  const now = Date.now();
  Object.keys(db.sessions).forEach(k => { if (now - db.sessions[k].ts > 90 * DAY) delete db.sessions[k]; });
  const t = randomBytes(32).toString("hex");
  db.sessions[sha(t)] = { uid, ts: now };
  return t;
}
const dropSessions = (db, uid) => Object.keys(db.sessions).forEach(k => { if (db.sessions[k].uid === uid) delete db.sessions[k]; });

function out(db, uid, extra) {
  const me = uid ? U(db, uid) : null, bs = blockedSet(db, uid);
  const admin = !!(me && ADMIN && me.handle === ADMIN);
  const posts = db.posts.filter(p => !bs.has(p.by)).sort((a, b) => b.ts - a.ts).map(p => ({
    ...p,
    comments: p.comments.map(c => bs.has(c.by) ? { hidden: true, replies: [] }
      : { ...c, replies: (c.replies || []).map(r => bs.has(r.by) ? { hidden: true } : r) })
  }));
  const r = {
    db: {
      profiles: db.users.map(u => pub(u, uid)), posts,
      lists: db.lists.filter(l => !bs.has(l.by)).sort((a, b) => b.ts - a.ts), pick: db.pick || null
    },
    clubs: db.clubs.filter(c => !!uid && c.members.includes(uid)).sort((a, b) => b.ts - a.ts).map(c => ({
      id: c.id, name: c.name, emoji: c.emoji, desc: c.desc, by: c.by, ts: c.ts, n: c.members.length, joined: true, m: c.members
    })),
    cmsgs: [],
    me: me ? me.id : null, msgs: [], notes: [], blocked: [], email: "", admin, reports: [], suspended: []
  };
  if (me) {
    r.msgs = db.msgs.filter(m => (m.from === uid || m.to === uid) && !bs.has(m.from === uid ? m.to : m.from)).sort((a, b) => a.ts - b.ts);
    r.notes = me.notes.filter(n => !bs.has(n.from));
    r.blocked = me.blocked.map(x => U(db, x)).filter(Boolean).map(u => pub(u, uid));
    r.email = me.email;
    if (admin) { r.reports = db.reports; r.suspended = db.suspended; }
  }
  return { ...r, ...extra };
}

async function sendReset(to, link) {
  const user = process.env.GMAIL_USER, pass = process.env.GMAIL_APP_PASSWORD;
  if (!user || !pass) { console.log("Email not configured: set GMAIL_USER and GMAIL_APP_PASSWORD"); return; }
  const t = nodemailer.createTransport({ host: "smtp.gmail.com", port: 465, secure: true, auth: { user, pass } });
  await t.sendMail({
    from: `Tangerine Review Club <${user}>`, to, subject: "Reset your Tangerine Review Club password",
    text: `Someone asked to reset your password.\n\nOpen this link within 1 hour to choose a new one:\n${link}\n\nIf this was not you, ignore this email.`,
    html: `<p>Someone asked to reset your password.</p><p><a href="${link}">Choose a new password</a> (valid for 1 hour)</p><p>If this was not you, ignore this email.</p>`
  });
}

export default async function handler(req, res) {
  res.setHeader("content-type", "application/json");
  res.setHeader("cache-control", "no-store");
  const send = o => res.status(200).send(JSON.stringify(o));
  if (req.method !== "POST") return send({ error: "Bad request" });
  let body = req.body;
  if (typeof body === "string") { try { body = JSON.parse(body); } catch (e) { return send({ error: "Bad request" }); } }
  if (!body || typeof body !== "object") return send({ error: "Bad request" });
  const a = String(body.a || ""), d = body.d && typeof body.d === "object" ? body.d : {};
  const origin = "https://" + (req.headers["x-forwarded-host"] || req.headers.host);

  let loaded;
  try { loaded = await load(); } catch (e) { console.error("Storage error:", e.message); return send({ error: "Storage is not set up yet" }); }
  const { db, raw } = loaded;

  const auth = (req.headers.authorization || "").replace(/^Bearer\s+/i, "").trim();
  let uid = null;
  const sess = auth && db.sessions[sha(auth)];
  if (sess && Date.now() - sess.ts < 90 * DAY) {
    const u = U(db, sess.uid);
    if (u && !db.suspended.includes(u.id)) uid = u.id;
  }
  const extra = {};
  let dirty = a !== "state" && a !== "read" && a !== "club";
  const C = id => db.clubs.find(c => c.id === id) || bad("Club not found");
  const me = () => (uid && U(db, uid)) || bad("Log in first");
  const P = id => db.posts.find(p => p.id === id) || bad("Post not found");
  const isAdmin = () => { const m = uid && U(db, uid); return !!(m && ADMIN && m.handle === ADMIN); };

  try {
    switch (a) {
      case "state": break;

      case "signup": {
        const name = clip(d.name, 30), handle = clip(d.handle, 20).toLowerCase().replace(/^@/, "");
        const email = clip(d.email, 120).toLowerCase(), pw = String(d.pw || "");
        if (!name) bad("Add a display name");
        if (!/^[a-z0-9_]{3,20}$/.test(handle)) bad("Username needs 3 to 20 letters, numbers or underscores");
        if (pw.length < 6 || pw.length > 100) bad("Password needs at least 6 characters");
        if (!emailOk(email)) bad("Enter a valid email");
        if (db.users.some(u => u.handle === handle)) bad("That username is taken");
        if (db.users.some(u => u.email === email)) bad("That email already has an account");
        const u = {
          id: id8(), name, handle, email, pw: hashPw(pw), bio: clip(d.bio, 160), avatar: clip(d.avatar, 8) || "🍊",
          following: [], top: cleanTop(d.top), ...cleanIg(d), watch: [], blocked: [], notes: []
        };
        db.users.push(u);
        uid = u.id; extra.token = newSession(db, u.id);
        break;
      }

      case "login": {
        const who = clip(d.handle, 120).toLowerCase().replace(/^@/, ""), key = sha(who), f = db.fails[key];
        if (f && f.until && f.until > Date.now()) bad("Too many tries. Wait a few minutes and try again.");
        const u = db.users.find(x => x.handle === who || x.email === who);
        if (!u || !checkPw(d.pw, u.pw)) {
          const n = ((f && f.n) || 0) + 1;
          db.fails[key] = n >= 8 ? { n: 0, until: Date.now() + 10 * 60000 } : { n, until: 0 };
          await save(db, raw);
          bad("Wrong username/email or password");
        }
        if (db.suspended.includes(u.id)) bad("This account has been suspended");
        delete db.fails[key];
        uid = u.id; extra.token = newSession(db, u.id);
        break;
      }

      case "logout": if (auth) delete db.sessions[sha(auth)]; uid = null; extra.token = ""; break;

      case "publish": {
        const m = me(), p = cleanPost(d);
        if (!p.rating) bad("Pick a star rating first");
        const post = { id: id8(), by: m.id, ...p, ts: Date.now(), likedBy: [], comments: [] };
        db.posts.push(post);
        if (d.wid) m.watch = m.watch.filter(w => w.id !== d.wid);
        mentions(db, post.text, m.id, post.id);
        break;
      }
      case "editpost": {
        const m = me(), p = P(d.id);
        if (p.by !== m.id) bad("You can only edit your own posts");
        const n = cleanPost(d);
        Object.assign(p, { type: n.type, media: n.media, title: n.title, text: n.text, spoiler: n.spoiler, rating: n.rating || p.rating, edited: true });
        break;
      }
      case "delete": {
        const m = me(), p = P(d.id);
        if (p.by !== m.id && !isAdmin()) bad("Not allowed");
        db.posts = db.posts.filter(x => x.id !== p.id);
        db.reports = db.reports.filter(r => r.pid !== p.id);
        break;
      }
      case "like": {
        const m = me(), p = P(d.id), i = p.likedBy.indexOf(m.id);
        if (i >= 0) p.likedBy.splice(i, 1); else { p.likedBy.push(m.id); note(db, p.by, "like", m.id, p.id); }
        break;
      }
      case "comment": {
        const m = me(), p = P(d.id), t = clip(d.t, 300);
        if (!t) bad("Write a comment first");
        p.comments.push({ by: m.id, t, ts: Date.now(), replies: [] });
        note(db, p.by, "comment", m.id, p.id); mentions(db, t, m.id, p.id);
        break;
      }
      case "editcomment": {
        const m = me(), p = P(d.id), c = p.comments[+d.i], t = clip(d.t, 300);
        if (!c || c.by !== m.id) bad("You can only edit your own comments");
        if (!t) bad("Comment cannot be empty");
        c.t = t; c.edited = true;
        break;
      }
      case "delcomment": {
        const m = me(), p = P(d.id), c = p.comments[+d.i];
        if (!c) bad("Comment not found");
        if (c.by !== m.id && p.by !== m.id && !isAdmin()) bad("Not allowed");
        p.comments.splice(+d.i, 1);
        break;
      }
      case "reply": {
        const m = me(), p = P(d.id), c = p.comments[+d.i], t = clip(d.t, 300);
        if (!c) bad("Comment not found");
        if (!t) bad("Write a reply first");
        (c.replies = c.replies || []).push({ by: m.id, t, ts: Date.now() });
        note(db, c.by, "reply", m.id, p.id); mentions(db, t, m.id, p.id);
        break;
      }
      case "delreply": {
        const m = me(), p = P(d.id), c = p.comments[+d.i], r = c && (c.replies || [])[+d.j];
        if (!r) bad("Reply not found");
        if (r.by !== m.id && p.by !== m.id && !isAdmin()) bad("Not allowed");
        c.replies.splice(+d.j, 1);
        break;
      }
      case "follow": {
        const m = me(), t = U(db, d.id);
        if (!t || t.id === m.id) bad("Cannot follow that account");
        const i = m.following.indexOf(t.id);
        if (i >= 0) m.following.splice(i, 1); else { m.following.push(t.id); note(db, t.id, "follow", m.id); }
        break;
      }
      case "saveprofile": {
        const m = me(), name = clip(d.name, 30), handle = clip(d.handle, 20).toLowerCase().replace(/^@/, "");
        if (!name) bad("Display name cannot be empty");
        if (!/^[a-z0-9_]{3,20}$/.test(handle)) bad("Username needs 3 to 20 letters, numbers or underscores");
        if (db.users.some(u => u.id !== m.id && u.handle === handle) || (ADMIN && handle === ADMIN && m.handle !== ADMIN)) bad("That username is taken");
        Object.assign(m, { name, handle, bio: clip(d.bio, 160), avatar: clip(d.avatar, 8) || m.avatar, top: cleanTop(d.top), ...cleanIg(d) });
        break;
      }
      case "message": {
        const m = me(), t = clip(d.t, 1000), to = U(db, d.id);
        if (!to || to.id === m.id) bad("Cannot message that account");
        if (!t) bad("Write a message first");
        if (blockedSet(db, m.id).has(to.id)) bad("You cannot message this person");
        db.msgs.push({ id: id8(), from: m.id, to: to.id, t, ts: Date.now(), read: false });
        break;
      }
      case "read": {
        const m = me();
        db.msgs.forEach(x => { if (x.to === m.id && x.from === d.id && !x.read) { x.read = true; dirty = true; } });
        break;
      }
      case "delmessage": {
        const m = me(), x = db.msgs.find(k => k.id === d.id);
        if (!x || x.from !== m.id) bad("You can only delete your own messages");
        db.msgs = db.msgs.filter(k => k.id !== x.id);
        break;
      }
      case "newclub": {
        const m = me(), name = clip(d.name, 40);
        if (!name) bad("Give your club a name");
        if (db.clubs.filter(c => c.by === m.id).length >= 5) bad("You can create up to 5 clubs");
        if (db.clubs.length >= 300) bad("There are too many clubs right now");
        const c = { id: id8(), name, emoji: clip(d.emoji, 8) || "🍊", desc: clip(d.desc, 140), by: m.id, ts: Date.now(), members: [m.id] };
        addPeople(db, c, m.id, d.members);
        db.clubs.push(c); extra.club = c.id;
        break;
      }
      case "addmembers": {
        const m = me(), c = C(d.id);
        if (!c.members.includes(m.id)) bad("Only members can add people");
        addPeople(db, c, m.id, d.members);
        break;
      }
      case "kick": {
        const m = me(), c = C(d.id);
        if (c.by !== m.id && !isAdmin()) bad("Only the club owner can remove people");
        if (d.uid === c.by) bad("The owner cannot be removed");
        c.members = c.members.filter(x => x !== d.uid);
        break;
      }
      case "leaveclub": {
        const m = me(), c = C(d.id);
        if (c.by === m.id) bad("You own this club. Delete it instead.");
        c.members = c.members.filter(x => x !== m.id);
        break;
      }
      case "club": {
        const m = me(), c = C(d.id);
        if (!c.members.includes(m.id)) bad("Join this club first");
        extra.cmsgs = clubMsgs(db, c.id, uid);
        break;
      }
      case "sendclub": {
        const m = me(), c = C(d.id), t = clip(d.t, 500);
        if (!c.members.includes(m.id)) bad("Join this club first");
        if (!t) bad("Write a message first");
        db.cmsgs.push({ id: id8(), club: c.id, by: m.id, t, ts: Date.now() });
        const mine = db.cmsgs.filter(x => x.club === c.id);
        if (mine.length > 500) { const drop = new Set(mine.slice(0, mine.length - 500)); db.cmsgs = db.cmsgs.filter(x => !drop.has(x)); }
        extra.cmsgs = clubMsgs(db, c.id, uid);
        break;
      }
      case "delclubmsg": {
        const m = me(), c = C(d.club), x = db.cmsgs.find(k => k.id === d.id && k.club === c.id);
        if (!x) bad("Message not found");
        if (x.by !== m.id && c.by !== m.id && !isAdmin()) bad("Not allowed");
        db.cmsgs = db.cmsgs.filter(k => k !== x);
        extra.cmsgs = clubMsgs(db, c.id, uid);
        break;
      }
      case "delclub": {
        const m = me(), c = C(d.id);
        if (c.by !== m.id && !isAdmin()) bad("Not allowed");
        db.clubs = db.clubs.filter(x => x !== c);
        db.cmsgs = db.cmsgs.filter(x => x.club !== c.id);
        break;
      }
      case "readnotes": me().notes.forEach(n => { n.read = true; }); break;

      case "addwatch": {
        const m = me(), type = clip(d.type, 20), media = clip(d.media, 80);
        if (!TYPES.includes(type) || !media) bad("Add a title first");
        if (m.watch.length >= 100) bad("Your watchlist is full");
        m.watch.push({ id: id8(), type, media });
        break;
      }
      case "delwatch": { const m = me(); m.watch = m.watch.filter(w => w.id !== d.id); break; }

      case "savelist": {
        const m = me(), title = clip(d.title, 80);
        const items = (Array.isArray(d.items) ? d.items : []).map(x => clip(x, 100)).filter(Boolean).slice(0, 30);
        if (!title) bad("Add a title first");
        if (d.id) {
          const l = db.lists.find(x => x.id === d.id);
          if (!l || l.by !== m.id) bad("You can only edit your own lists");
          Object.assign(l, { title, items, edited: true });
        } else db.lists.push({ id: id8(), by: m.id, title, items, ts: Date.now() });
        break;
      }
      case "dellist": {
        const m = me(), l = db.lists.find(x => x.id === d.id);
        if (!l || (l.by !== m.id && !isAdmin())) bad("Not allowed");
        db.lists = db.lists.filter(x => x.id !== l.id);
        break;
      }

      case "forgot": {
        const who = clip(d.who, 120).toLowerCase().replace(/^@/, "");
        const u = who && db.users.find(x => x.handle === who || x.email === who);
        if (u && !db.suspended.includes(u.id)) {
          const t = randomBytes(32).toString("hex");
          Object.keys(db.resets).forEach(k => { if (db.resets[k].exp < Date.now()) delete db.resets[k]; });
          db.resets[sha(t)] = { uid: u.id, exp: Date.now() + 3600000 };
          await save(db, raw);
          try { await sendReset(u.email, origin + "/#reset=" + t); } catch (e) { console.error("Mail failed:", e.message); }
        }
        break;
      }
      case "resetpw": {
        const pw = String(d.pw || ""), r = db.resets[sha(d.token || "")];
        if (pw.length < 6 || pw.length > 100) bad("New password needs at least 6 characters");
        if (!r || r.exp < Date.now()) bad("This reset link has expired. Ask for a new one.");
        const u = U(db, r.uid);
        if (!u) bad("Account not found");
        u.pw = hashPw(pw);
        delete db.resets[sha(d.token)];
        dropSessions(db, u.id);
        uid = u.id; extra.token = newSession(db, u.id);
        break;
      }
      case "setemail": {
        const m = me(), email = clip(d.email, 120).toLowerCase();
        if (!checkPw(d.pw, m.pw)) bad("Wrong password");
        if (!emailOk(email)) bad("Enter a valid email");
        if (db.users.some(u => u.id !== m.id && u.email === email)) bad("That email already has an account");
        m.email = email;
        break;
      }
      case "changepw": {
        const m = me(), pw = String(d.pw || "");
        if (!checkPw(d.old, m.pw)) bad("Current password is wrong");
        if (pw.length < 6 || pw.length > 100) bad("New password needs at least 6 characters");
        m.pw = hashPw(pw);
        break;
      }
      case "deleteaccount": {
        const m = me();
        if (!checkPw(d.pw, m.pw)) bad("Wrong password");
        const id = m.id;
        db.users = db.users.filter(u => u.id !== id);
        db.users.forEach(u => { u.following = u.following.filter(x => x !== id); u.blocked = u.blocked.filter(x => x !== id); u.notes = u.notes.filter(n => n.from !== id); });
        db.posts = db.posts.filter(p => p.by !== id);
        db.posts.forEach(p => {
          p.likedBy = p.likedBy.filter(x => x !== id);
          p.comments = p.comments.filter(c => c.by !== id);
          p.comments.forEach(c => { c.replies = (c.replies || []).filter(r => r.by !== id); });
        });
        db.clubs.forEach(c => { c.members = c.members.filter(x => x !== id); });
        const gone = new Set(db.clubs.filter(c => c.by === id).map(c => c.id));
        db.clubs = db.clubs.filter(c => c.by !== id);
        db.cmsgs = db.cmsgs.filter(x => x.by !== id && !gone.has(x.club));
        db.lists = db.lists.filter(l => l.by !== id);
        db.msgs = db.msgs.filter(x => x.from !== id && x.to !== id);
        db.reports = db.reports.filter(r => r.by !== id && db.posts.some(p => p.id === r.pid));
        db.suspended = db.suspended.filter(x => x !== id);
        dropSessions(db, id);
        uid = null; extra.token = "";
        break;
      }

      case "setpick": {
        if (!isAdmin()) bad("Admins only");
        const type = clip(d.type, 20), media = clip(d.media, 80);
        db.pick = media && TYPES.includes(type) ? { type, media, note: clip(d.note, 200) } : null;
        break;
      }
      case "report": {
        const m = me(), kind = d.k === "comment" ? "comment" : "post", p = P(d.id);
        const i = kind === "comment" ? +d.i : undefined;
        if (db.reports.some(r => r.by === m.id && r.pid === p.id && r.i === i && r.kind === kind)) break;
        db.reports.push({ id: id8(), kind, by: m.id, pid: p.id, i, reason: clip(d.reason, 200), ts: Date.now() });
        if (db.reports.length > 200) db.reports.shift();
        break;
      }
      case "dismissreport": if (!isAdmin()) bad("Admins only"); db.reports = db.reports.filter(r => r.id !== d.id); break;
      case "block": {
        const m = me(), t = U(db, d.id);
        if (!t || t.id === m.id) bad("Cannot block that account");
        const i = m.blocked.indexOf(t.id);
        if (i >= 0) m.blocked.splice(i, 1);
        else { m.blocked.push(t.id); m.following = m.following.filter(x => x !== t.id); t.following = t.following.filter(x => x !== m.id); }
        break;
      }
      case "suspend": {
        const m = me(), t = U(db, d.id);
        if (!isAdmin()) bad("Admins only");
        if (!t || t.id === m.id) bad("Cannot suspend that account");
        const i = db.suspended.indexOf(t.id);
        if (i >= 0) db.suspended.splice(i, 1); else { db.suspended.push(t.id); dropSessions(db, t.id); }
        break;
      }
      default: bad("Unknown action");
    }
  } catch (e) {
    if (e instanceof E) return send({ error: e.message });
    console.error(e);
    return send({ error: "Something went wrong, try again" });
  }
  if (dirty) await save(db, raw);
  return send(out(db, uid, extra));
}
