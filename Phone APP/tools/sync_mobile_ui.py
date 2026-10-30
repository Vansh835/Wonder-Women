"""Copy the current Flask mobile template into the Android app's bundled assets."""
from __future__ import annotations

import ast
import json
from pathlib import Path


PHONE_APP_DIR = Path(__file__).resolve().parents[1]
PROJECT_ROOT = PHONE_APP_DIR.parent
PYTHON_APP = PROJECT_ROOT / "saheli_ai.py"
ASSET_FILE = PHONE_APP_DIR / "app" / "src" / "main" / "assets" / "www" / "index.html"

ANDROID_FETCH_BOOTSTRAP = r"""<script>
(function(){
  let apiBase = "", apiToken = "";
  window.setPhoneApiConfig = function(base, token) {
    apiBase = String(base || "").trim().replace(/\/+$/, "");
    apiToken = String(token || "").trim();
  };
  const originalFetch = window.fetch.bind(window);
  window.fetch = function(input, init) {
    const path = typeof input === "string" ? input : input.url;
    if (typeof path === "string" && path.startsWith("/")) {
      if (!apiBase) return Promise.reject(new Error("Open Computer API settings and enter the server address."));
      const options = Object.assign({}, init || {});
      const headers = new Headers(options.headers || {});
      if (apiToken) headers.set("X-Safety-Token", apiToken);
      options.headers = headers;
      return originalFetch(apiBase + path, options);
    }
    return originalFetch(input, init);
  };
  window.testPhoneApi = async function() {
    try {
      const response = await window.fetch("/pin/status");
      if (!response.ok) throw new Error("HTTP " + response.status);
      return "Connected to the computer API.";
    } catch (error) {
      return "Connection failed: " + (error.message || "check address, token, and Wi-Fi");
    }
  };
})();
</script>"""


def assign_value(tree: ast.Module, name: str):
    for node in tree.body:
        if isinstance(node, ast.Assign):
            if any(isinstance(target, ast.Name) and target.id == name for target in node.targets):
                return ast.literal_eval(node.value)
    raise ValueError(f"Could not find literal assignment for {name}")


def main() -> None:
    tree = ast.parse(PYTHON_APP.read_text(encoding="utf-8"))
    html = assign_value(tree, "MOBILE_HTML_TEMPLATE")
    places = assign_value(tree, "COMMON_DELHI_PLACES")
    helplines = [
        {"name": "Emergency (all services)", "number": "112"},
        {"name": "Women Helpline", "number": "1091"},
        {"name": "Women Helpline", "number": "181"},
        {"name": "Child Helpline", "number": "1098"},
        {"name": "Police", "number": "100"},
        {"name": "Cyber Crime", "number": "1930"},
        {"name": "National Commission for Women", "number": "7827170170"},
    ]
    html = html.replace("__HELPLINES__", json.dumps(helplines, ensure_ascii=False))
    html = html.replace("__COMMON_PLACES__", json.dumps(places, ensure_ascii=False))
    html = html.replace("<head>", "<head>\n" + ANDROID_FETCH_BOOTSTRAP, 1)

    old_audio = """function playFakeVoice() {
    const file = document.getElementById('fakeVoice').value;
    if (file) {
        callAudio = new Audio('/fake_call_audio/' + encodeURIComponent(file));
        callAudio.loop = true;      // repeats until the call is ended
        callAudio.volume = 1;
        callAudio.play().catch(() => speakScript());   // if the file cannot play, use the built-in voice
    } else {
        speakScript();
    }
}"""
    new_audio = """async function playFakeVoice() {
    const file = document.getElementById('fakeVoice').value;
    if (file) {
        try {
            const response = await fetch('/fake_call_audio/' + encodeURIComponent(file));
            if (!response.ok) throw new Error('Recording unavailable');
            callAudio = new Audio(URL.createObjectURL(await response.blob()));
            callAudio.loop = true;
            callAudio.volume = 1;
            await callAudio.play();
        } catch (_) { speakScript(); }
    } else {
        speakScript();
    }
}"""
    if old_audio not in html:
        raise ValueError("Could not find the mobile fake-call audio function")
    html = html.replace(old_audio, new_audio, 1)
    ASSET_FILE.parent.mkdir(parents=True, exist_ok=True)
    ASSET_FILE.write_text(html, encoding="utf-8")
    print(f"Updated {ASSET_FILE}")


if __name__ == "__main__":
    main()
