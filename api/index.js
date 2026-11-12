import { Redis } from "@upstash/redis";
import { gzipSync, gunzipSync } from "node:zlib";
import nodemailer from "nodemailer";
import { randomBytes, randomUUID, scryptSync, timingSafeEqual, createHash } from "node:crypto";

const redis = Redis.fromEnv({ automaticDeserialization: false });
const PIECES = ["users", "posts", "lists", "msgs", "clubs", "cmsgs", "features", "meta", "tposts"];
const META = ["reports", "pick", "suspended", "sessions", "resets", "fails", "core", "admins", "banner", "prompts", "polls", "bingos", "reposts", "about", "times", "crew", "tstaff"];
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
  if (Array.isArray(db.core)) { const o = {}; db.core.forEach(x => { o[x] = "writer"; }); db.core = o; }
  /* Zest Team roles are now a list, so one person can be a writer and an editor.
     Old single roles are converted: "writer" stays a writer, "editor" keeps both abilities it had before. */
  Object.keys(db.core).forEach(k => {
    const v = db.core[k];
    if (typeof v === "string") db.core[k] = v === "editor" ? ["writer", "editor"] : ["writer"];
    else if (!Array.isArray(v)) delete db.core[k];
  });
  if (!db.crew || typeof db.crew !== "object" || Array.isArray(db.crew)) db.crew = {};
  if (!db.tstaff || typeof db.tstaff !== "object" || Array.isArray(db.tstaff)) db.tstaff = {};
  if (!Array.isArray(db.tposts)) db.tposts = [];
  db.polls.forEach(l => { if (l.kind === "thisthat" && !l.pairs) { l.pairs = [l.options]; Object.keys(l.votes).forEach(u => { l.votes[u] = { 0: l.votes[u] }; }); l.options = []; } });
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
const CREW_TEAMS = ["Editorial", "Crew"];
const TSEC = ["movies", "books", "games", "music", "culture", "magazine"];
const TROLES = ["publisher", "writer", "artist"];
const DAY = 864e5;
const ADMINS = (process.env.ADMIN_HANDLE || "").split(/[,\s]+/).map(x => x.trim().toLowerCase().replace(/^@/, "")).filter(Boolean);
const isAdminHandle = h => ADMINS.includes(h);
const isAdminU = (db, u) => !!(u && (isAdminHandle(u.handle) || db.admins.includes(u.id)));
const rolesOf = (db, id) => (id && Array.isArray(db.core[id]) ? db.core[id] : []);
const tRolesOf = (db, id) => (id && Array.isArray(db.tstaff[id]) ? db.tstaff[id] : []);

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
const fresh = () => ({ users: [], posts: [], lists: [], msgs: [], clubs: [], cmsgs: [], features: [], core: {}, crew: {}, tstaff: {}, tposts: [], admins: [], banner: null, about: null, times: null, prompts: [], polls: [], bingos: [], reposts: [], reports: [], pick: null, suspended: [], sessions: {}, resets: {}, fails: {} });
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
function cleanPost(d, draft) {
  let type = clip(d.type, 20), media = clip(d.media, 80), title = clip(d.title, 100), text = clip(d.text, 10000);
  if (draft) {
    if (!TYPES.includes(type)) type = "Other";
    if (!title) bad("Add a headline to save a draft");
  } else {
    if (!TYPES.includes(type)) bad("Pick a media type");
    if (!media || !title || !text) bad("Add a media title, headline and review first");
  }
  const r = parseInt(d.rating, 10);
  return { type, media, title, text, rating: r >= 1 && r <= 5 ? r : 0, spoiler: !!d.spoiler };
}
function cleanFeature(d) {
  const title = clip(d.title, 120), dek = clip(d.dek, 200), tag = clip(d.tag, 30), text = clip(d.text, 20000);
  const type = TYPES.includes(clip(d.type, 20)) ? clip(d.type, 20) : "", media = clip(d.media, 80);
  if (!title || !text) bad("Add a headline and the article text first");
  return { title, dek, tag, text, type, media: type ? media : "" };
}
const cleanPron = d => clip(Array.isArray(d.pronouns) ? d.pronouns.join(" / ") : d.pronouns, 30);
const esc = s => String(s).replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
const pub = (u, viewer) => ({
  id: u.id, name: u.name, handle: u.handle, bio: u.bio, avatar: u.avatar, following: u.following, top: u.top, pronouns: Array.isArray(u.pronouns) ? u.pronouns.join(" / ") : (u.pronouns || ""), bingoShares: u.bingoShares || [],
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
  const admin = isAdminU(db, me), owner = !!(me && isAdminHandle(me.handle));
  const canTimes = !!(me && (admin || tRolesOf(db, me.id).includes("publisher")));
  const posts = db.posts.filter(p => !bs.has(p.by) && (!p.draft || p.by === uid)).sort((a, b) => b.ts - a.ts).map(p => ({
    ...p,
    likedBy: p.likedBy.filter(x => !bs.has(x)),
    comments: p.comments.map(c => bs.has(c.by) ? { hidden: true, replies: [] }
      : { ...c, replies: (c.replies || []).map(r => bs.has(r.by) ? { hidden: true } : r) })
  }));
  const myRoles = me ? rolesOf(db, me.id) : [];
  const isCore = !!(me && (admin || myRoles.length));
  const isEditor = !!(me && (admin || myRoles.includes("editor")));
  const canWrite = !!(me && (admin || myRoles.includes("writer")));
  const seeF = f => isEditor || (me && f.by === me.id) || (f.status === "published" && !bs.has(f.by));
  const features = db.features.filter(seeF).sort((a, b) => (b.publishedAt || b.ts) - (a.publishedAt || a.ts));
  const r = {
    features, isCore, isEditor, canWrite, core: admin ? db.core : {}, owner, admins: owner ? db.admins : [],
    db: {
      profiles: db.users.map(u => ({ ...pub(u, uid), crew: db.crew[u.id] ? (db.crew[u.id] === "Editorial" ? "Editorial" : "Crew") : "" })), posts,
      reposts: db.reposts.filter(r => !bs.has(r.by) && posts.some(p => p.id === r.pid && !p.draft)),
      lists: db.lists.filter(l => !bs.has(l.by)).sort((a, b) => b.ts - a.ts).map(l => ({
        ...l,
        comments: (l.comments || []).map((c, i) => ({ ...c, i })).filter(c => !bs.has(c.by))
      })),
      pick: db.pick || null,
      banner: db.banner || null,
      about: db.about || null,
      times: db.times || null,
      tposts: db.tposts.slice().sort((x, y) => y.ts - x.ts).map(({ pub, ...p }) => p),
      tstaff: admin || canTimes ? db.tstaff : {},
      canTimes,
      bingos: db.bingos.slice().sort((a, b) => b.ts - a.ts).map(l => ({ id: l.id, title: l.title, cells: l.cells, ts: l.ts, marks: uid && l.marks[uid] ? l.marks[uid] : [] })),
      prompts: db.prompts.slice().sort((a, b) => b.ts - a.ts),
      polls: db.polls.slice().sort((a, b) => b.ts - a.ts).map(l => {
        if (l.kind === "thisthat") {
          const pairs = l.pairs.map((pr, i) => {
            let na = 0, nb = 0;
            Object.values(l.votes).forEach(v => { if (v && v[i] === 0) na++; else if (v && v[i] === 1) nb++; });
            return { a: pr[0], b: pr[1], na, nb };
          });
          const mv = uid && l.votes[uid] && typeof l.votes[uid] === "object" ? l.votes[uid] : {};
          return { id: l.id, q: l.q, kind: l.kind, closed: !!l.closed, ts: l.ts, options: [], pairs, mine: l.pairs.map((_, i) => (mv[i] === 0 || mv[i] === 1 ? mv[i] : -1)) };
        }
        const n = l.options.map(() => 0);
        Object.values(l.votes).forEach(v => { if (typeof v === "number" && n[v] !== undefined) n[v]++; });
        return { id: l.id, q: l.q, kind: l.kind, closed: !!l.closed, ts: l.ts, options: l.options.map((t, i) => ({ t, n: n[i] })), mine: uid && typeof l.votes[uid] === "number" ? l.votes[uid] : -1 };
      })
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
    if (admin) {
      r.reports = db.reports; r.suspended = db.suspended;
    }
    if (owner) {
      r.members = db.users.map(u => ({ id: u.id, email: u.email || "", joined: u.joined || 0, everSuspended: !!u.everSuspended || db.suspended.includes(u.id), insta: u.insta || "" }));
    }
  }
  return { ...r, ...extra };
}

async function sendMail(to, subject, text, html) {
  const user = (process.env.GMAIL_USER || "").trim(), pass = (process.env.GMAIL_APP_PASSWORD || "").replace(/\s+/g, "");
  if (!user || !pass) throw new Error("Email is not set up. Add GMAIL_USER and GMAIL_APP_PASSWORD in Vercel, then redeploy.");
  if (!to) throw new Error("No email address to send to");
  const t = nodemailer.createTransport({ host: "smtp.gmail.com", port: 465, secure: true, auth: { user, pass } });
  await t.sendMail({ from: `Tangerine Review Club <${user}>`, to, subject, text, html });
}
const sendReset = (to, link) => sendMail(to, "Reset your Tangerine Review Club password",
  `Someone asked to reset your password.\n\nOpen this link within 1 hour to choose a new one:\n${link}\n\nIf this was not you, ignore this email.`,
  `<p>Someone asked to reset your password.</p><p><a href="${link}">Choose a new password</a> (valid for 1 hour)</p><p>If this was not you, ignore this email.</p>`);

export default async function handler(req, res) {
  if (req.method === "GET" && req.query && req.query.img) {
    const iid = String(req.query.img).replace(/[^a-z0-9]/gi, "").slice(0, 20);
    try {
      const b64 = iid ? await redis.get("tg:img:" + iid) : null;
      if (!b64 || typeof b64 !== "string") { res.status(404).end(); return; }
      res.setHeader("content-type", "image/jpeg");
      res.setHeader("cache-control", "public, max-age=31536000, immutable");
      res.status(200).send(Buffer.from(b64, "base64"));
    } catch (e) { console.error("Image error:", e.message); res.status(500).end(); }
    return;
  }
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
  const mails = [];
  const F = id => db.features.find(f => f.id === id) || bad("Piece not found");
  let dirty = a !== "state" && a !== "read" && a !== "club";
  const C = id => db.clubs.find(c => c.id === id) || bad("Club not found");
  const me = () => (uid && U(db, uid)) || bad("Log in first");
  const P = id => db.posts.find(p => p.id === id) || bad("Post not found");
  const isAdmin = () => isAdminU(db, uid && U(db, uid));
  const isOwner = () => { const m = uid && U(db, uid); return !!(m && isAdminHandle(m.handle)); };
  const isEditor = () => isAdmin() || rolesOf(db, uid).includes("editor");

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
          joined: Date.now(), following: [], top: cleanTop(d.top), pronouns: cleanPron(d), ...cleanIg(d), watch: [], blocked: [], notes: []
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
        const m = me(), draft = !!d.draft, p = cleanPost(d, draft);
        if (!draft && !p.rating) bad("Pick a star rating first");
        const post = { id: id8(), by: m.id, ...p, ts: Date.now(), likedBy: [], comments: [] };
        if (draft) post.draft = true;
        const pr = d.prompt && db.prompts.find(x => x.id === d.prompt);
        if (pr) post.prompt = pr.id;
        db.posts.push(post);
        if (!draft) {
          if (d.wid) m.watch = m.watch.filter(w => w.id !== d.wid);
          mentions(db, post.text, m.id, post.id);
        }
        break;
      }
      case "editpost": {
        const m = me(), p = P(d.id);
        if (p.by !== m.id) bad("You can only edit your own posts");
        const keepDraft = !!p.draft && !!d.draft;
        const n = cleanPost(d, keepDraft);
        if (p.draft && !keepDraft && !(n.rating || p.rating)) bad("Pick a star rating first");
        Object.assign(p, { type: n.type, media: n.media, title: n.title, text: n.text, spoiler: n.spoiler, rating: n.rating || p.rating });
        if (p.draft && !keepDraft) { delete p.draft; p.ts = Date.now(); mentions(db, p.text, m.id, p.id); }
        else if (!p.draft) p.edited = true;
        break;
      }
      case "delete": {
        const m = me(), p = P(d.id);
        if (p.by !== m.id && !isAdmin()) bad("Not allowed");
        db.posts = db.posts.filter(x => x.id !== p.id);
        db.reports = db.reports.filter(r => r.pid !== p.id);
        db.reposts = db.reposts.filter(r => r.pid !== p.id);
        break;
      }
      case "repost": {
        const m = me(), p = P(d.id);
        if (p.draft) bad("Drafts cannot be reposted");
        if (p.by === m.id) bad("You cannot repost your own post");
        if (blockedSet(db, m.id).has(p.by)) bad("Not allowed");
        const i = db.reposts.findIndex(r => r.pid === p.id && r.by === m.id);
        if (i >= 0) db.reposts.splice(i, 1);
        else { db.reposts.push({ id: id8(), pid: p.id, by: m.id, ts: Date.now() }); note(db, p.by, "repost", m.id, p.id); }
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
        if (db.users.some(u => u.id !== m.id && u.handle === handle) || (isAdminHandle(handle) && !isAdminHandle(m.handle))) bad("That username is taken");
        Object.assign(m, { name, handle, bio: clip(d.bio, 160), avatar: clip(d.avatar, 8) || m.avatar, top: cleanTop(d.top), pronouns: cleanPron(d), ...cleanIg(d) });
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
        } else db.lists.push({ id: id8(), by: m.id, title, items, ts: Date.now(), comments: [] });
        break;
      }
      case "dellist": {
        const m = me(), l = db.lists.find(x => x.id === d.id);
        if (!l || (l.by !== m.id && !isAdmin())) bad("Not allowed");
        db.lists = db.lists.filter(x => x.id !== l.id);
        break;
      }
      case "lcomment": {
        const m = me(), l = db.lists.find(x => x.id === d.id) || bad("List not found"), t = clip(d.t, 300);
        if (blockedSet(db, m.id).has(l.by)) bad("Not allowed");
        if (!t) bad("Write a comment first");
        l.comments = l.comments || [];
        if (l.comments.length >= 200) bad("This list has too many comments");
        l.comments.push({ by: m.id, t, ts: Date.now() });
        break;
      }
      case "ldelcomment": {
        const m = me(), l = db.lists.find(x => x.id === d.id) || bad("List not found"), i = parseInt(d.i, 10);
        const c = (l.comments || [])[i];
        if (!c) bad("Comment not found");
        if (c.by !== m.id && l.by !== m.id && !isAdmin()) bad("Not allowed");
        l.comments.splice(i, 1);
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
        db.reposts = db.reposts.filter(r => r.by !== id && db.posts.some(p => p.id === r.pid));
        db.lists = db.lists.filter(l => l.by !== id);
        db.lists.forEach(l => { l.comments = (l.comments || []).filter(c => c.by !== id); });
        db.clubs.forEach(c => { c.members = c.members.filter(x => x !== id); });
        const gone = new Set(db.clubs.filter(c => c.by === id).map(c => c.id));
        db.clubs = db.clubs.filter(c => c.by !== id);
        db.cmsgs = db.cmsgs.filter(x => x.by !== id && !gone.has(x.club));
        db.features = db.features.filter(f => f.by !== id);
        delete db.core[id];
        delete db.crew[id];
        delete db.tstaff[id];
        db.tposts.forEach(x => { if (x.by === id) x.by = ""; if (x.art === id) x.art = ""; if (x.layout === id) x.layout = ""; });
        db.admins = db.admins.filter(x => x !== id);
        db.polls.forEach(l => { delete l.votes[id]; });
        db.bingos.forEach(l => { delete l.marks[id]; });
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
      case "setabout": {
        if (!isAdmin()) bad("Admins only");
        const head = clip(d.head, 200), body = clip(d.body, 3000);
        db.about = head || body ? { head, body, ts: Date.now() } : null;
        break;
      }
      case "settimes": {
        if (!isAdmin()) bad("Admins only");
        const head = clip(d.head, 200), body = clip(d.body, 3000), about = clip(d.about, 3000);
        const joinHead = clip(d.joinHead, 100), joinBody = clip(d.joinBody, 500), joinEmail = clip(d.joinEmail, 120).toLowerCase();
        if (joinEmail && !emailOk(joinEmail)) bad("Enter a valid email for the join box");
        db.times = head || body || about || joinHead || joinBody || joinEmail ? { head, body, about, joinHead, joinBody, joinEmail, ts: Date.now() } : null;
        break;
      }
      case "setcrew": {
        if (!isAdmin()) bad("Admins only");
        const t = U(db, d.id);
        if (!t) bad("Member not found");
        const team = CREW_TEAMS.includes(d.team) ? d.team : "";
        if (team) db.crew[t.id] = team; else delete db.crew[t.id];
        break;
      }
      case "tpost": {
        const m = me();
        if (!isAdmin() && !tRolesOf(db, m.id).includes("publisher")) bad("Only publishers can post in the Times");
        const sec = TSEC.includes(d.sec) ? d.sec : bad("Pick a section");
        const title = clip(d.title, 140), text = clip(d.text, 20000);
        if (!title) bad("Add a headline first");
        if (!text) bad("Add the content first");
        const credit = (v, role, what) => {
          v = clip(v, 20);
          if (!v) return "";
          if (!U(db, v) || !tRolesOf(db, v).includes(role)) bad(what + " must be someone on the Times team");
          return v;
        };
        const by = credit(d.by, "writer", "The writer"), art = credit(d.art, "artist", "The artist"), layout = credit(d.layout, "artist", "The layout artist");
        const old = d.id ? (db.tposts.find(x => x.id === d.id) || bad("Piece not found")) : null;
        let img = old ? old.img || "" : "";
        if (typeof d.data === "string" && d.data) {
          const mm = /^data:image\/jpeg;base64,([A-Za-z0-9+/=]+)$/.exec(d.data);
          if (!mm || d.data.length > 700000) bad("That photo could not be used. Try another one.");
          const nid = id8() + id8();
          await redis.set("tg:img:" + nid, mm[1]);
          if (img) await redis.del("tg:img:" + img);
          img = nid;
        } else if (!d.keepImg && img) {
          await redis.del("tg:img:" + img);
          img = "";
        }
        if (old) { Object.assign(old, { sec, title, text, by, art, layout, img, edited: true }); extra.tid = old.id; }
        else {
          if (db.tposts.length >= 500) bad("Delete some old Times pieces first");
          const np = { id: id8(), sec, title, text, by, art, layout, img, ts: Date.now(), pub: m.id };
          db.tposts.push(np); extra.tid = np.id;
        }
        break;
      }
      case "tdel": {
        const m = me();
        if (!isAdmin() && !tRolesOf(db, m.id).includes("publisher")) bad("Not allowed");
        const tp = db.tposts.find(x => x.id === d.id) || bad("Piece not found");
        if (tp.img) { try { await redis.del("tg:img:" + tp.img); } catch (e) { console.error(e.message); } }
        db.tposts = db.tposts.filter(x => x !== tp);
        break;
      }
      case "settstaff": {
        if (!isAdmin()) bad("Admins only");
        const t = U(db, d.id);
        if (!t) bad("Member not found");
        if (!TROLES.includes(d.role)) bad("Unknown role");
        const cur = tRolesOf(db, t.id).filter(r => r !== d.role);
        if (d.on) cur.push(d.role);
        if (cur.length) db.tstaff[t.id] = TROLES.filter(r => cur.includes(r)); else delete db.tstaff[t.id];
        break;
      }
      case "mailtest": {
        if (!isAdmin()) bad("Admins only");
        const m = me();
        try { await sendMail(m.email, "Tangerine test email", "Email is working.", "<p>Email is working. 🍊</p>"); extra.mail = "Test email sent to " + m.email + ". Check your inbox and spam."; }
        catch (e) { extra.mail = "Email failed: " + e.message; }
        break;
      }
      case "setcore": {
        if (!isAdmin()) bad("Admins only");
        const t = U(db, d.id);
        if (!t) bad("Member not found");
        const want = Array.isArray(d.roles) ? d.roles : (d.role ? [d.role] : []);
        const roles = ["writer", "editor"].filter(r => want.includes(r));
        if (roles.length) db.core[t.id] = roles; else delete db.core[t.id];
        break;
      }
      case "fsave": {
        const m = me(), admin = isAdmin(), ed = isEditor(), roles = rolesOf(db, m.id);
        if (!roles.length && !admin) bad("Feature Picks is for the Zest Team only");
        if (!d.id && !admin && !roles.includes("writer")) bad("You need the Writer role to write a piece");
        const n = cleanFeature(d);
        let author = m;
        if (d.as) {
          if (!admin) bad("Admins only");
          const h = clip(d.as, 20).toLowerCase().replace(/^@/, "");
          author = db.users.find(u => u.handle === h) || bad("Author not found");
          if (author.id !== m.id && !rolesOf(db, author.id).length) bad("That member is not on the Zest Team");
        }
        let f;
        if (d.id) {
          f = F(d.id);
          if (f.by !== m.id && !ed) bad("You can only edit your own pieces");
          if (f.status === "published" && !ed) bad("Published pieces can only be changed by an editor");
          Object.assign(f, n, { edited: true });
          if (!ed && f.status !== "pending") { f.status = "pending"; f.note = ""; }
        } else {
          f = { id: id8(), by: author.id, ...n, status: "pending", via: d.as ? "email" : "site", ts: Date.now(), publishedAt: 0, note: "" };
          db.features.push(f);
        }
        if (ed && d.publish) { f.status = "published"; f.publishedAt = Date.now(); f.note = ""; }
        if (!ed && f.status === "pending") {
          db.users.filter(u => isAdminU(db, u) || rolesOf(db, u.id).includes("editor")).forEach(rv => mails.push(() => sendMail(rv.email, "Feature Picks: new piece to review",
            `${author.name} (@${author.handle}) submitted "${f.title}" for Feature Picks.\n\nReview it here:\n${origin}/#feature-picks`,
            `<p><b>${esc(author.name)}</b> (@${esc(author.handle)}) submitted <b>${esc(f.title)}</b> for Feature Picks.</p><p><a href="${origin}/#feature-picks">Review it</a></p>`)));
        }
        break;
      }
      case "fdecide": {
        if (!isEditor()) bad("Editors only");
        const f = F(d.id), to = d.to;
        if (!["published", "rejected", "pending"].includes(to)) bad("Unknown status");
        f.status = to; f.note = clip(d.note, 500);
        f.publishedAt = to === "published" ? Date.now() : 0;
        const au = U(db, f.by);
        if (au && to !== "pending") {
          const ok = to === "published", subj = ok ? "Your Feature Picks piece is live" : "Feedback on your Feature Picks piece";
          const body = ok ? `"${f.title}" has been published on Feature Picks.\n${origin}/#feature-picks` : `"${f.title}" was not published this time.${f.note ? "\n\nEditor's note: " + f.note : ""}\n\nYou can edit it and send it again.`;
          mails.push(() => sendMail(au.email, subj, body, "<p>" + esc(body).replace(/\n/g, "<br>") + "</p>"));
        }
        break;
      }
      case "fdelete": {
        const m = me(), f = F(d.id);
        if (!isEditor() && !(f.by === m.id && f.status !== "published")) bad("Not allowed");
        db.features = db.features.filter(x => x.id !== f.id);
        break;
      }
      case "setadmin": {
        if (!isOwner()) bad("Only the owner can change the admin list");
        const t = U(db, d.id);
        if (!t) bad("Member not found");
        if (isAdminHandle(t.handle)) bad("That person is already an owner");
        const i = db.admins.indexOf(t.id);
        if (d.on && i < 0) db.admins.push(t.id);
        if (!d.on && i >= 0) db.admins.splice(i, 1);
        break;
      }
      case "setbanner": {
        if (!isAdmin()) bad("Admins only");
        const title = clip(d.title, 100), text = clip(d.text, 1000);
        if (!title && text) bad("Add a headline for the announcement");
        db.banner = title ? { title, text, ts: Date.now() } : null;
        break;
      }
      case "saveprompt": {
        if (!isAdmin()) bad("Admins only");
        const title = clip(d.title, 100);
        if (!title) bad("Write the prompt first");
        if (d.id) {
          const k = db.prompts.find(x => x.id === d.id) || bad("Prompt not found");
          Object.assign(k, { title, desc: clip(d.desc, 300), edited: true });
          break;
        }
        if (db.prompts.length >= 100) bad("Delete some old prompts first");
        db.prompts.push({ id: id8(), title, desc: clip(d.desc, 300), by: uid, ts: Date.now() });
        break;
      }
      case "delprompt": {
        if (!isAdmin()) bad("Admins only");
        db.prompts = db.prompts.filter(x => x.id !== d.id);
        break;
      }
      case "savepoll": {
        if (!isAdmin()) bad("Admins only");
        const old = d.id ? (db.polls.find(x => x.id === d.id) || bad("Poll not found")) : null;
        const kind = old ? old.kind : (d.kind === "thisthat" ? "thisthat" : "poll"), q = clip(d.q, 120);
        const lines = (Array.isArray(d.options) ? d.options : []).map(x => clip(x, 100)).filter(Boolean);
        if (!q) bad("Write the question or title first");
        if (!old && db.polls.length >= 100) bad("Delete some old polls first");
        let options = [], pairs;
        if (kind === "thisthat") {
          pairs = lines.map(x => x.split("|").map(y => clip(y, 40))).filter(a => a.length >= 2 && a[0] && a[1]).map(a => [a[0], a[1]]);
          if (pairs.length !== lines.length) bad("Each line needs two choices with a | between them, like: Pizza | Burgers");
          if (pairs.length < 3 || pairs.length > 9) bad("This or that needs 3 to 9 lines (you have " + pairs.length + ")");
        } else {
          options = lines.map(x => clip(x, 60)).slice(0, 6);
          if (options.length < 2) bad("Add at least 2 options, one per line");
        }
        if (old) { Object.assign(old, { q, options, pairs, edited: true }); break; }
        db.polls.push({ id: id8(), by: uid, q, kind, options, pairs, votes: {}, ts: Date.now(), closed: false });
        break;
      }
      case "pollvote": {
        const m = me(), l = db.polls.find(x => x.id === d.id) || bad("Poll not found");
        if (l.closed) bad("This is closed");
        const i = parseInt(d.i, 10);
        if (l.kind === "thisthat") {
          const c = parseInt(d.c, 10);
          if (!(i >= 0 && i < l.pairs.length) || (c !== 0 && c !== 1)) bad("Pick one");
          const v = l.votes[m.id] && typeof l.votes[m.id] === "object" ? l.votes[m.id] : (l.votes[m.id] = {});
          v[i] = c;
        } else {
          if (!(i >= 0 && i < l.options.length)) bad("Pick an option");
          l.votes[m.id] = i;
        }
        break;
      }
      case "pollclose": {
        if (!isAdmin()) bad("Admins only");
        const l = db.polls.find(x => x.id === d.id) || bad("Poll not found");
        l.closed = !l.closed;
        break;
      }
      case "delpoll": {
        if (!isAdmin()) bad("Admins only");
        db.polls = db.polls.filter(x => x.id !== d.id);
        break;
      }
      case "savebingo": {
        if (!isAdmin()) bad("Admins only");
        const title = clip(d.title, 80), cells = (Array.isArray(d.cells) ? d.cells : []).map(x => clip(x, 40)).filter(Boolean);
        if (!title) bad("Give the bingo card a title");
        if (cells.length !== 25) bad("A bingo card needs exactly 25 squares, one per line (you have " + cells.length + ")");
        if (d.id) {
          const l = db.bingos.find(x => x.id === d.id) || bad("Bingo card not found");
          Object.assign(l, { title, cells, edited: true });
          break;
        }
        if (db.bingos.length >= 50) bad("Delete some old bingo cards first");
        db.bingos.push({ id: id8(), by: uid, title, cells, marks: {}, ts: Date.now() });
        break;
      }
      case "delbingo": {
        if (!isAdmin()) bad("Admins only");
        db.bingos = db.bingos.filter(x => x.id !== d.id);
        break;
      }
      case "bingomark": {
        const m = me(), l = db.bingos.find(x => x.id === d.id) || bad("Bingo card not found");
        const i = parseInt(d.i, 10);
        if (!(i >= 0 && i < 25)) bad("Pick a square");
        const a2 = l.marks[m.id] || (l.marks[m.id] = []), k = a2.indexOf(i);
        if (k >= 0) a2.splice(k, 1); else a2.push(i);
        break;
      }
      case "bingoshare": {
        const m = me(), l = db.bingos.find(x => x.id === d.id) || bad("Bingo card not found");
        m.bingoShares = (m.bingoShares || []).filter(x => x.id !== l.id);
        m.bingoShares.push({ id: l.id, title: l.title, cells: l.cells, marks: (l.marks[m.id] || []).slice(), ts: Date.now() });
        if (m.bingoShares.length > 20) m.bingoShares.shift();
        break;
      }
      case "bingounshare": {
        const m = me();
        m.bingoShares = (m.bingoShares || []).filter(x => x.id !== d.id);
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
        if (i >= 0) db.suspended.splice(i, 1); else { db.suspended.push(t.id); t.everSuspended = true; dropSessions(db, t.id); }
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
  if (mails.length) await Promise.allSettled(mails.map(f => f()));
  return send(out(db, uid, extra));
}
