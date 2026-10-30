package com.womensafety.phoneapp;

import android.Manifest;
import android.app.Activity;
import android.app.AlarmManager;
import android.app.AlertDialog;
import android.app.PendingIntent;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.content.pm.PackageManager;
import android.hardware.Sensor;
import android.hardware.SensorEvent;
import android.hardware.SensorEventListener;
import android.hardware.SensorManager;
import android.graphics.Color;
import android.net.Uri;
import android.os.Bundle;
import android.os.Build;
import android.text.InputType;
import android.text.method.PasswordTransformationMethod;
import android.view.Gravity;
import android.view.View;
import android.webkit.GeolocationPermissions;
import android.webkit.JavascriptInterface;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceRequest;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.speech.RecognitionListener;
import android.speech.RecognizerIntent;
import android.speech.SpeechRecognizer;
import android.widget.Button;
import android.widget.EditText;
import android.widget.LinearLayout;
import android.widget.TextView;

import androidx.webkit.WebViewAssetLoader;
import androidx.webkit.WebViewClientCompat;

import org.json.JSONObject;
import org.json.JSONTokener;

import java.net.URI;
import java.util.ArrayList;

public final class MainActivity extends Activity implements SensorEventListener {
    private static final String PREFS = "phone_api_settings";
    private static final String KEY_BASE = "base_url";
    private static final String KEY_TOKEN = "pairing_token";
    private static final String ASSET_ORIGIN = "https://appassets.androidplatform.net";
    private static final String START_PAGE = ASSET_ORIGIN + "/assets/www/index.html";
    private static final int LOCATION_PERMISSION_REQUEST = 7201;
    private static final int NOTIFICATION_PERMISSION_REQUEST = 7202;
    private static final int AUDIO_PERMISSION_REQUEST = 7203;

    private SharedPreferences preferences;
    private WebView webView;
    private TextView connectionStatus;
    private GeolocationPermissions.Callback pendingLocationCallback;
    private String pendingLocationOrigin;
    private SpeechRecognizer speechRecognizer;
    private SensorManager sensorManager;
    private Sensor accelerometer;
    private long lastShakeAt;
    private float lastAcceleration;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        preferences = getSharedPreferences(PREFS, MODE_PRIVATE);
        sensorManager = (SensorManager) getSystemService(SENSOR_SERVICE);
        if (sensorManager != null) accelerometer = sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER);
        setContentView(createLayout());
        configureWebView();
        if (!getBaseUrl().isEmpty()) updateConnectionLabel();
        else webView.postDelayed(() -> showApiSettings(true), 450);
    }

    private View createLayout() {
        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setBackgroundColor(Color.rgb(16, 25, 29));

        LinearLayout bar = new LinearLayout(this);
        bar.setOrientation(LinearLayout.HORIZONTAL);
        bar.setGravity(Gravity.CENTER_VERTICAL);
        bar.setPadding(dp(10), dp(6), dp(10), dp(6));
        bar.setBackgroundColor(Color.rgb(23, 35, 41));

        connectionStatus = new TextView(this);
        connectionStatus.setTextColor(Color.WHITE);
        connectionStatus.setTextSize(12);
        connectionStatus.setMaxLines(1);
        connectionStatus.setEllipsize(android.text.TextUtils.TruncateAt.MIDDLE);
        bar.addView(connectionStatus, new LinearLayout.LayoutParams(0, dp(42), 1));

        Button test = new Button(this);
        test.setText("Test");
        test.setOnClickListener(v -> testConnection());
        bar.addView(test, new LinearLayout.LayoutParams(dp(72), dp(42)));

        Button settings = new Button(this);
        settings.setText("Server");
        settings.setOnClickListener(v -> showApiSettings(false));
        LinearLayout.LayoutParams settingsParams = new LinearLayout.LayoutParams(dp(82), dp(42));
        settingsParams.leftMargin = dp(6);
        bar.addView(settings, settingsParams);

        root.addView(bar, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT));

        webView = new WebView(this);
        root.addView(webView, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, 0, 1));
        return root;
    }

    private void configureWebView() {
        WebSettings settings = webView.getSettings();
        settings.setJavaScriptEnabled(true);
        settings.setDomStorageEnabled(true);
        settings.setGeolocationEnabled(true);
        settings.setAllowFileAccess(false);
        settings.setAllowContentAccess(false);
        settings.setMixedContentMode(BuildConfig.DEBUG
                ? WebSettings.MIXED_CONTENT_ALWAYS_ALLOW
                : WebSettings.MIXED_CONTENT_NEVER_ALLOW);

        WebViewAssetLoader assetLoader = new WebViewAssetLoader.Builder()
                .setDomain("appassets.androidplatform.net")
                .addPathHandler("/assets/", new WebViewAssetLoader.AssetsPathHandler(this))
                .build();

        webView.setWebViewClient(new WebViewClientCompat() {
            @Override
            public android.webkit.WebResourceResponse shouldInterceptRequest(
                    WebView view, WebResourceRequest request) {
                return assetLoader.shouldInterceptRequest(request.getUrl());
            }

            @Override
            public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) {
                return handleNavigation(request.getUrl());
            }

            @Override
            public void onPageFinished(WebView view, String url) {
                super.onPageFinished(view, url);
                if (url.startsWith(ASSET_ORIGIN + "/assets/")) pushApiConfigToPage();
            }
        });

        webView.addJavascriptInterface(new CheckInBridge(), "SafetyNative");

        webView.setWebChromeClient(new WebChromeClient() {
            @Override
            public void onGeolocationPermissionsShowPrompt(
                    String origin, GeolocationPermissions.Callback callback) {
                if (!origin.equals(ASSET_ORIGIN)) {
                    callback.invoke(origin, false, false);
                    return;
                }
                boolean fine = checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION)
                        == PackageManager.PERMISSION_GRANTED;
                boolean coarse = checkSelfPermission(Manifest.permission.ACCESS_COARSE_LOCATION)
                        == PackageManager.PERMISSION_GRANTED;
                if (fine || coarse) {
                    callback.invoke(origin, true, false);
                } else {
                    pendingLocationOrigin = origin;
                    pendingLocationCallback = callback;
                    requestPermissions(new String[]{
                            Manifest.permission.ACCESS_FINE_LOCATION,
                            Manifest.permission.ACCESS_COARSE_LOCATION
                    }, LOCATION_PERMISSION_REQUEST);
                }
            }
        });

        webView.loadUrl(START_PAGE);
    }

    private void ensureCheckInChannel() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.O) return;
        NotificationManager manager = getSystemService(NotificationManager.class);
        if (manager != null) manager.createNotificationChannel(new NotificationChannel(
                CheckInReceiver.CHANNEL_ID, "Check-in reminders", NotificationManager.IMPORTANCE_HIGH));
    }

    private final class CheckInBridge {
        @JavascriptInterface
        public void setShakeSOS(boolean enabled) {
            preferences.edit().putBoolean("shake_sos", enabled).apply();
            runOnUiThread(() -> { if (enabled) registerShakeSensor(); else unregisterShakeSensor(); });
        }

        @JavascriptInterface
        public String startVoiceRecognition(String language) {
            if (checkSelfPermission(Manifest.permission.RECORD_AUDIO) != PackageManager.PERMISSION_GRANTED) {
                runOnUiThread(() -> requestPermissions(new String[]{Manifest.permission.RECORD_AUDIO}, AUDIO_PERMISSION_REQUEST));
                return "permission_required";
            }
            if (!SpeechRecognizer.isRecognitionAvailable(MainActivity.this)) return "unavailable";
            runOnUiThread(() -> beginNativeSpeech(language));
            return "started";
        }

        @JavascriptInterface
        public void stopVoiceRecognition() {
            runOnUiThread(() -> {
                if (speechRecognizer != null) {
                    try { speechRecognizer.cancel(); speechRecognizer.destroy(); } catch (Exception ignored) { }
                    speechRecognizer = null;
                }
                if (webView != null) webView.evaluateJavascript("window.onNativeSpeechStopped && window.onNativeSpeechStopped()", null);
            });
        }

        @JavascriptInterface
        public String scheduleCheckIn(String idText, long whenMillis, String phone, String message) {
            if (Build.VERSION.SDK_INT >= 33 && checkSelfPermission(Manifest.permission.POST_NOTIFICATIONS)
                    != PackageManager.PERMISSION_GRANTED) {
                runOnUiThread(() -> requestPermissions(new String[]{Manifest.permission.POST_NOTIFICATIONS},
                        NOTIFICATION_PERMISSION_REQUEST));
                return "permission_required";
            }
            try {
                ensureCheckInChannel();
                int id = Math.abs(idText == null ? 1 : idText.hashCode());
                Intent alarmIntent = new Intent(MainActivity.this, CheckInReceiver.class)
                        .putExtra("id", id)
                        .putExtra(CheckInReceiver.EXTRA_PHONE, phone)
                        .putExtra(CheckInReceiver.EXTRA_MESSAGE, message);
                PendingIntent pending = PendingIntent.getBroadcast(MainActivity.this, id, alarmIntent,
                        PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);
                AlarmManager alarms = (AlarmManager) getSystemService(Context.ALARM_SERVICE);
                if (alarms == null) return "unavailable";
                alarms.setAndAllowWhileIdle(AlarmManager.RTC_WAKEUP, whenMillis, pending);
                return "scheduled";
            } catch (Exception ignored) { return "unavailable"; }
        }

        @JavascriptInterface
        public void cancelCheckIn(String idText) {
            try {
                int id = Math.abs(idText == null ? 1 : idText.hashCode());
                Intent intent = new Intent(MainActivity.this, CheckInReceiver.class);
                PendingIntent pending = PendingIntent.getBroadcast(MainActivity.this, id, intent,
                        PendingIntent.FLAG_NO_CREATE | PendingIntent.FLAG_IMMUTABLE);
                if (pending != null) {
                    AlarmManager alarms = (AlarmManager) getSystemService(Context.ALARM_SERVICE);
                    if (alarms != null) alarms.cancel(pending);
                    pending.cancel();
                }
            } catch (Exception ignored) { }
        }
    }

    private void registerShakeSensor() {
        if (sensorManager != null && accelerometer != null)
            sensorManager.registerListener(this, accelerometer, SensorManager.SENSOR_DELAY_UI);
    }

    private void unregisterShakeSensor() {
        if (sensorManager != null) sensorManager.unregisterListener(this);
    }

    @Override protected void onResume() {
        super.onResume();
        if (preferences != null && preferences.getBoolean("shake_sos", false)) registerShakeSensor();
    }

    @Override protected void onPause() {
        unregisterShakeSensor();
        super.onPause();
    }

    @Override public void onSensorChanged(SensorEvent event) {
        if (event.sensor.getType() != Sensor.TYPE_ACCELEROMETER || webView == null) return;
        float x = event.values[0], y = event.values[1], z = event.values[2];
        float acceleration = (float) Math.sqrt(x * x + y * y + z * z);
        long now = System.currentTimeMillis();
        if (acceleration > 24f && lastAcceleration < 16f && now - lastShakeAt > 1800) {
            lastShakeAt = now;
            runOnUiThread(() -> webView.evaluateJavascript("window.triggerShakeSOS && window.triggerShakeSOS()", null));
        }
        lastAcceleration = acceleration;
    }

    @Override public void onAccuracyChanged(Sensor sensor, int accuracy) { }

    private void beginNativeSpeech(String language) {
        if (speechRecognizer != null) {
            try { speechRecognizer.destroy(); } catch (Exception ignored) { }
        }
        speechRecognizer = SpeechRecognizer.createSpeechRecognizer(this);
        speechRecognizer.setRecognitionListener(new RecognitionListener() {
            @Override public void onReadyForSpeech(Bundle params) { }
            @Override public void onBeginningOfSpeech() { }
            @Override public void onRmsChanged(float rmsdB) { }
            @Override public void onBufferReceived(byte[] buffer) { }
            @Override public void onEndOfSpeech() { }
            @Override public void onError(int error) {
                if (webView != null) webView.evaluateJavascript("window.onNativeSpeechError && window.onNativeSpeechError(" + error + ")", null);
                if (speechRecognizer != null) { speechRecognizer.destroy(); speechRecognizer = null; }
            }
            @Override public void onResults(Bundle results) {
                ArrayList<String> matches = results.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION);
                if (matches != null && !matches.isEmpty() && webView != null) {
                    webView.evaluateJavascript("window.onNativeSpeechResult && window.onNativeSpeechResult(" + JSONObject.quote(matches.get(0)) + ")", null);
                }
                if (speechRecognizer != null) { speechRecognizer.destroy(); speechRecognizer = null; }
            }
            @Override public void onPartialResults(Bundle partialResults) { }
            @Override public void onEvent(int eventType, Bundle params) { }
        });
        Intent intent = new Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH);
        intent.putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM);
        intent.putExtra(RecognizerIntent.EXTRA_LANGUAGE, language == null ? "hi-IN" : language);
        intent.putExtra(RecognizerIntent.EXTRA_PARTIAL_RESULTS, false);
        speechRecognizer.startListening(intent);
    }

    private boolean handleNavigation(Uri uri) {
        String scheme = uri.getScheme() == null ? "" : uri.getScheme().toLowerCase();
        if ("tel".equals(scheme) || "sms".equals(scheme)) {
            try {
                Intent intent = new Intent("tel".equals(scheme)
                        ? Intent.ACTION_DIAL : Intent.ACTION_SENDTO, uri);
                startActivity(intent);
            } catch (Exception ignored) { }
            return true;
        }
        if ("https".equals(scheme) && "appassets.androidplatform.net".equals(uri.getHost())) {
            return false;
        }
        if ("https".equals(scheme) || "http".equals(scheme)) {
            try { startActivity(new Intent(Intent.ACTION_VIEW, uri)); }
            catch (Exception ignored) { }
        }
        return true;
    }

    private void showApiSettings(boolean firstRun) {
        LinearLayout form = new LinearLayout(this);
        form.setOrientation(LinearLayout.VERTICAL);
        form.setPadding(dp(22), dp(8), dp(22), 0);

        TextView instructions = new TextView(this);
        instructions.setText("Start the computer app with --phone-api. Enter its Wi-Fi address and the one-run pairing token shown in its console.");
        instructions.setTextSize(14);
        form.addView(instructions);

        EditText address = new EditText(this);
        address.setSingleLine(true);
        address.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_URI);
        address.setHint("https://computer.example  (debug: http://192.168.1.20:5000)");
        address.setText(getBaseUrl());
        form.addView(address);

        EditText token = new EditText(this);
        token.setSingleLine(true);
        token.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_PASSWORD);
        token.setTransformationMethod(PasswordTransformationMethod.getInstance());
        token.setHint("Pairing token from computer console");
        token.setText(getToken());
        form.addView(token);

        AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle(firstRun ? "Connect to your computer" : "Computer API")
                .setView(form)
                .setPositiveButton("Save", null)
                .setNegativeButton(firstRun ? "Later" : "Cancel", (d, which) -> { })
                .create();
        dialog.setOnShowListener(ignored -> dialog.getButton(AlertDialog.BUTTON_POSITIVE)
                .setOnClickListener(v -> {
                    String base = address.getText().toString().trim();
                    base = base.replaceAll("/+$", "");
                    String pairingToken = token.getText().toString().trim();
                    if (!isAllowedBaseUrl(base)) {
                        address.setError("Use an HTTPS server. Debug builds may use a private Wi-Fi IP or .local host.");
                        return;
                    }
                    if (pairingToken.length() < 32) {
                        token.setError("Enter the complete pairing token from the computer console.");
                        return;
                    }
                    preferences.edit().putString(KEY_BASE, base)
                            .putString(KEY_TOKEN, pairingToken).apply();
                    updateConnectionLabel();
                    pushApiConfigToPage();
                    dialog.dismiss();
                }));
        dialog.show();
    }

    private boolean isAllowedBaseUrl(String value) {
        try {
            URI uri = URI.create(value);
            if (uri.getHost() == null || uri.getUserInfo() != null || uri.getQuery() != null
                    || uri.getFragment() != null || (uri.getPath() != null
                    && !uri.getPath().isEmpty() && !"/".equals(uri.getPath()))) return false;
            if ("https".equalsIgnoreCase(uri.getScheme())) return true;
            return BuildConfig.DEBUG && "http".equalsIgnoreCase(uri.getScheme())
                    && isPrivateLanHost(uri.getHost());
        } catch (Exception ignored) { return false; }
    }

    private boolean isPrivateLanHost(String host) {
        String h = host.toLowerCase();
        if (h.endsWith(".local")) return true;
        String[] parts = h.split("\\.");
        if (parts.length != 4) return false;
        try {
            int a = Integer.parseInt(parts[0]), b = Integer.parseInt(parts[1]);
            int c = Integer.parseInt(parts[2]), d = Integer.parseInt(parts[3]);
            if (a < 0 || a > 255 || b < 0 || b > 255 || c < 0 || c > 255 || d < 0 || d > 255) return false;
            return a == 10 || (a == 192 && b == 168) || (a == 172 && b >= 16 && b <= 31);
        } catch (NumberFormatException ignored) { return false; }
    }

    private void testConnection() {
        if (getBaseUrl().isEmpty()) {
            showApiSettings(false);
            return;
        }
        connectionStatus.setText("Checking computer…");
        webView.evaluateJavascript("window.testPhoneApi()", value -> {
            try {
                Object result = new JSONTokener(value).nextValue();
                connectionStatus.setText(String.valueOf(result));
            } catch (Exception ignored) {
                connectionStatus.setText("Could not read connection status.");
            }
        });
    }

    private void pushApiConfigToPage() {
        if (webView == null) return;
        String base = JSONObject.quote(getBaseUrl());
        String token = JSONObject.quote(getToken());
        webView.evaluateJavascript("window.setPhoneApiConfig(" + base + "," + token + ")", null);
    }

    private String getBaseUrl() { return preferences.getString(KEY_BASE, ""); }
    private String getToken() { return preferences.getString(KEY_TOKEN, ""); }

    private void updateConnectionLabel() {
        String base = getBaseUrl();
        connectionStatus.setText(base.isEmpty() ? "Computer API not configured" : "Computer: " + base);
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        if (requestCode == LOCATION_PERMISSION_REQUEST && pendingLocationCallback != null) {
            boolean granted = false;
            for (int result : grantResults) granted |= result == PackageManager.PERMISSION_GRANTED;
            pendingLocationCallback.invoke(pendingLocationOrigin, granted, false);
            pendingLocationCallback = null;
            pendingLocationOrigin = null;
        }
    }

    @Override
    public void onBackPressed() {
        if (webView != null && webView.canGoBack()) webView.goBack();
        else super.onBackPressed();
    }

    @Override
    protected void onDestroy() {
        if (speechRecognizer != null) {
            try { speechRecognizer.cancel(); speechRecognizer.destroy(); } catch (Exception ignored) { }
            speechRecognizer = null;
        }
        if (webView != null) {
            webView.stopLoading();
            webView.destroy();
        }
        super.onDestroy();
    }

    private int dp(int value) {
        return Math.round(value * getResources().getDisplayMetrics().density);
    }
}
