#!/bin/bash
cd ..
./gradlew assemble
java -jar build/libs/crowbar.jar --full examples/account.abs