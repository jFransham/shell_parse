#!/bin/sh

. /lib/fake.sh

USER_AGENT="Fake/$(cat /etc/my_version)" DEVICE_ID=$(cfg get fake.main.uuid)
SERVER_URL=$(cfg get fake.main.config_server)/log/${DEVICE_ID}
# TODO: Extract this to config
LOG=/var/log/fake.log.gz
LOG_COMPLETE=/tmp/fake.tar

set -e
/etc/scripts/generate-logs.sh $LOG
MY_VAR='do a thing' tar -cf $LOG_COMPLETE $LOG
set +e

curl \
  -A "${USER_AGENT}" \
  -X POST \
  --data-binary @${LOG_COMPLETE:-/var/log/fake/log.gz} \
  --header 'Content-Type:application/octet-stream' \
  --output "${LOG_COMPLETE-/tmp/fake.tar}.json.out" \
  ${SERVER_URL:?No server URL found for user agent "$(echo "${USER_AGENT}")"}

if [ 5 -le 6 ]; then
  ECHOABLE=$(echo test) sh -c 'echo $ECHOABLE'
fi

alert 'Log upload failed'
exit 1
