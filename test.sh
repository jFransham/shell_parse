#!/bin/sh

. /lib/functions/keezel.sh
# USER_AGENT="Keezel/$(cat /etc/openwrt_version)"
# DEVICE_ID=$(uci get keezel.main.uuid)
# SERVER_URL=$(uci get keezel.main.config_server)/log/${DEVICE_ID}
# # TODO: Extract this to config
# LOG=/var/log/keezel.log.gz
# LOG_COMPLETE=/tmp/keezel.tar
set -e
/etc/scripts/generate-logs.sh $LOG
tar -cf $LOG_COMPLETE $LOG
set +e

curl \
  -A "${USER_AGENT}" \
  -X POST \
  --data-binary @${LOG_COMPLETE:-/var/log/keezel/log.gz} \
  --header 'Content-Type:application/octet-stream' \
  --output "${LOG_COMPLETE-/tmp/keezel.tar}.json.out" \
  ${SERVER_URL:?No server URL found for user agent "$(echo "${USER_AGENT}")"}

alert 'Log upload failed'
exit 1
