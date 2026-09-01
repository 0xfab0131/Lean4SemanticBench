/* ============================================================
   js/persist.js — 読み込んだレポートとピンの保持

   このアプリは file:// で開く前提なので、出力した report.jsonl を
   fetch で読むことができない（opaque origin で拒否される）。
   毎回 5 MB を投げ直させないために、一度読んだものは IndexedDB に置く。

   localStorage ではなく IndexedDB なのは容量の問題。
   実データは 5 MB 級で、localStorage の上限をそのまま越える。
   ============================================================ */
(function (LDR) {
  "use strict";

  const DB_NAME = "ldr", STORE = "kv", VERSION = 1;
  let dbp = null;

  function db() {
    if (dbp) return dbp;
    dbp = new Promise((res, rej) => {
      if (!("indexedDB" in window)) { rej(new Error("IndexedDB がありません")); return; }
      const rq = indexedDB.open(DB_NAME, VERSION);
      rq.onupgradeneeded = () => { rq.result.createObjectStore(STORE); };
      rq.onsuccess = () => res(rq.result);
      rq.onerror = () => rej(rq.error);
    });
    return dbp;
  }

  function tx(mode, fn) {
    return db().then((d) => new Promise((res, rej) => {
      const t = d.transaction(STORE, mode);
      const st = t.objectStore(STORE);
      let out;
      const r = fn(st);
      if (r) r.onsuccess = () => { out = r.result; };
      t.oncomplete = () => res(out);
      t.onerror = () => rej(t.error);
      t.onabort = () => rej(t.error);
    }));
  }

  const get = (k) => tx("readonly", (st) => st.get(k)).catch(() => undefined);
  const set = (k, v) => tx("readwrite", (st) => st.put(v, k)).catch(() => undefined);
  const del = (k) => tx("readwrite", (st) => st.delete(k)).catch(() => undefined);

  /** 連続する保存をまとめる。データ本体は大きいので毎打鍵で書かない。 */
  function debounced(fn, ms) {
    let t = null;
    return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); };
  }

  LDR.persist = { get, set, del, debounced };
})(window.LDR = window.LDR || {});
