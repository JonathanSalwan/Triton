#! /usr/bin/env bash

echo "[+] Testing data instructions (ARM)..." && \
python unicorn_test_arm32_data_arm.py && \

echo "[+] Testing data instructions (Thumb)..."  && \
python unicorn_test_arm32_data_thumb.py && \

echo "[+] Testing branch instructions (ARM)..."  && \
python unicorn_test_arm32_branch_arm_1.py && \
python unicorn_test_arm32_branch_arm_2.py && \

echo "[+] Testing branch instructions (Thumb)..."  && \
python unicorn_test_arm32_branch_thumb_1.py && \
python unicorn_test_arm32_branch_thumb_2.py && \

echo "[+] Testing branch (via PC manipulation) instructions (ARM)..."  && \
python unicorn_test_arm32_branch_pc_arm_1.py && \
python unicorn_test_arm32_branch_pc_arm_2.py && \

echo "[+] Testing load/store instructions (ARM)..."  && \
python unicorn_test_arm32_loadstore_arm_1.py && \
python unicorn_test_arm32_loadstore_arm_2.py && \
python unicorn_test_arm32_loadstore_arm_3.py && \

echo "[+] Testing load/store instructions (Thumb)..."  && \
python unicorn_test_arm32_loadstore_thumb_1.py && \
python unicorn_test_arm32_loadstore_thumb_2.py && \
python unicorn_test_arm32_loadstore_thumb_3.py && \

echo "[+] Testing interworking (ARM -> Thumb -> ARM)..."  && \
python unicorn_test_arm32_interworking_arm.py && \

echo "[+] Testing interworking (Thumb -> ARM -> Thumb)..."  && \
python unicorn_test_arm32_interworking_thumb.py
