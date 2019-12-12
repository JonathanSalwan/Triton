#! /usr/bin/env bash

echo "[+] Testing data instruction (ARM)..." && \
python unicorn_test_arm32_data_arm.py && \

echo "[+] Testing data instruction (Thumb)..."  && \
python unicorn_test_arm32_data_thumb.py && \

echo "[+] Testing branch instruction (ARM)..."  && \
python unicorn_test_arm32_branch_arm_1.py && \
python unicorn_test_arm32_branch_arm_2.py && \

echo "[+] Testing branch instruction (Thumb)..."  && \
python unicorn_test_arm32_branch_thumb_1.py && \
python unicorn_test_arm32_branch_thumb_2.py && \

echo "[+] Testing branch (via PC manipulation) instruction (ARM)..."  && \
python unicorn_test_arm32_branch_pc_arm_1.py && \
python unicorn_test_arm32_branch_pc_arm_2.py

echo "[+] Testing interworking (ARM -> Thumb -> ARM)..."  && \
python unicorn_test_arm32_interworking_arm.py && \

echo "[+] Testing interworking (Thumb -> ARM -> Thumb)..."  && \
python unicorn_test_arm32_interworking_thumb.py
