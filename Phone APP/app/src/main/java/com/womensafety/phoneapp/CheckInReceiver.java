package com.womensafety.phoneapp;

import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.net.Uri;
import android.os.Build;

import androidx.core.app.NotificationCompat;

public final class CheckInReceiver extends BroadcastReceiver {
    static final String CHANNEL_ID = "check_in_alerts";
    static final String EXTRA_PHONE = "phone";
    static final String EXTRA_MESSAGE = "message";

    @Override
    public void onReceive(Context context, Intent intent) {
        NotificationManager manager = (NotificationManager) context.getSystemService(Context.NOTIFICATION_SERVICE);
        if (manager == null) return;
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            manager.createNotificationChannel(new NotificationChannel(
                    CHANNEL_ID, "Check-in reminders", NotificationManager.IMPORTANCE_HIGH));
        }

        String phone = intent.getStringExtra(EXTRA_PHONE);
        String message = intent.getStringExtra(EXTRA_MESSAGE);
        Intent sms = new Intent(Intent.ACTION_SENDTO, Uri.parse("smsto:" + Uri.encode(phone == null ? "" : phone)));
        sms.putExtra("sms_body", message == null ? "I missed my check-in. Please call me." : message);
        PendingIntent openSms = PendingIntent.getActivity(context, intent.getIntExtra("id", 1), sms,
                PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);

        manager.notify(intent.getIntExtra("id", 1), new NotificationCompat.Builder(context, CHANNEL_ID)
                .setSmallIcon(android.R.drawable.ic_dialog_alert)
                .setContentTitle("Check-in reminder")
                .setContentText("Your check-in timer ended. Tap to review and send the prepared SMS.")
                .setStyle(new NotificationCompat.BigTextStyle().bigText("Your check-in timer ended. Tap to review the message and send it to your trusted contact."))
                .setContentIntent(openSms)
                .setAutoCancel(true)
                .setPriority(NotificationCompat.PRIORITY_HIGH)
                .build());
    }
}
