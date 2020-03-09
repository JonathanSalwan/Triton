#! /usr/bin/env bash

scripts_path=$(dirname $0)

echo "[+] Running ./crypto_test-nothumb-O0-run.py ..."
status=$(python $scripts_path/crypto_test-nothumb-O0-run.py | grep "^ko" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-nothumb-O0-run.py"

echo "[+] Running ./crypto_test-nothumb-O1-run.py ..."
status=$(python $scripts_path/crypto_test-nothumb-O1-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-nothumb-O1-run.py"

echo "[+] Running ./crypto_test-nothumb-O2-run.py ..."
status=$(python $scripts_path/crypto_test-nothumb-O2-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-nothumb-O2-run.py"

echo "[+] Running ./crypto_test-nothumb-O3-run.py ..."
status=$(python $scripts_path/crypto_test-nothumb-O3-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-nothumb-O3-run.py"

echo "[+] Running ./crypto_test-nothumb-Os-run.py ..."
status=$(python $scripts_path/crypto_test-nothumb-Os-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-nothumb-Os-run.py"

echo "[+] Running ./crypto_test-nothumb-Oz-run.py ..."
status=$(python $scripts_path/crypto_test-nothumb-Oz-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-nothumb-Oz-run.py"

echo "[+] Running ./crypto_test-thumb-O0-run.py ..."
status=$(python $scripts_path/crypto_test-thumb-O0-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-thumb-O0-run.py"

echo "[+] Running ./crypto_test-thumb-O1-run.py ..."
status=$(python $scripts_path/crypto_test-thumb-O1-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-thumb-O1-run.py"

echo "[+] Running ./crypto_test-thumb-O2-run.py ..."
status=$(python $scripts_path/crypto_test-thumb-O2-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-thumb-O2-run.py"

echo "[+] Running ./crypto_test-thumb-O3-run.py ..."
status=$(python $scripts_path/crypto_test-thumb-O3-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-thumb-O3-run.py"

echo "[+] Running ./crypto_test-thumb-Os-run.py ..."
status=$(python $scripts_path/crypto_test-thumb-Os-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-thumb-Os-run.py"

echo "[+] Running ./crypto_test-thumb-Oz-run.py ..."
status=$(python $scripts_path/crypto_test-thumb-Oz-run.py | grep "^ok" > /dev/null; if [ $? -eq 0 ]; then echo OK; else echo KO; fi)
echo "[$status] Running ./crypto_test-thumb-Oz-run.py"
