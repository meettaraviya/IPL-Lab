
	.data
global_maxn:	.word	0

	.text	# The .text assembler directive indicates
	.globl factorial	# The following is the code
factorial:
# Prologue begins
	sw $ra, 0($sp)	# Save the return address
	sw $fp, -4($sp)	# Save the frame pointer
	sub $fp, $sp, 8	# Update the frame pointer
	sub $sp, $sp, 16	# Make space for the locals
# Prologue ends
label0:
	lw $s0, 4($sp)
	lw $s1, 0($s0)
	lw $s0, 8($sp)
	sw $s1, 0($s0)
	j label1
label1:
	lw $s0, 8($sp)
	lw $s1, 0($s0)
	lw $s0, 20($sp)
	lw $s2, 0($s0)
	slt $s0, $s1, $s2
	move $s1, $s0
	bne $s1, $0, label2
	j label3
label2:
	lw $s0, 4($sp)
	lw $s1, 0($s0)
	lw $s0, 8($sp)
	lw $s2, 0($s0)
	mul $s0, $s1, $s2
	move $s1, $s0
	lw $s0, 4($sp)
	sw $s1, 0($s0)
	lw $s0, 8($sp)
	lw $s1, 0($s0)
	li $s0, 1
	add $s2, $s1, $s0
	move $s0, $s2
	lw $s1, 8($sp)
	sw $s0, 0($s1)
	j label1
label3:
	lw $s0, 4($sp)
	move $v1, $s0 # move return value to $v1
	j epilogue_factorial

# Epilogue begins
epilogue_factorial:
	add $sp, $sp, 16
	lw $fp, -4($sp)
	lw $ra, 0($sp)
	jr $ra	# Jump back to the called procedure
# Epilogue ends
	.text	# The .text assembler directive indicates
	.globl main	# The following is the code
main:
# Prologue begins
	sw $ra, 0($sp)	# Save the return address
	sw $fp, -4($sp)	# Save the frame pointer
	sub $fp, $sp, 8	# Update the frame pointer
	sub $sp, $sp, 24	# Make space for the locals
# Prologue ends
label4:
	li $s0, 1
	lw $s1, 16($sp)
	sw $s0, 0($s1)
	li $s0, 3
	lw $s1, 4($sp)
	sw $s0, 0($s1)
	li $s0, 100000
	lw $s1, global_maxn
	sw $s0, 0($s1)
	# setting up activation record for called function
	lw $s0, 4($sp)
	sw $s0, -4($sp)
	lw $s0, 16($sp)
	sw $s0, 0($sp)
	sub $sp, $sp, 8
	jal factorial # function call
	add $sp, $sp, 8 # destroying activation record of called function
	move $s0, $v1 # using the return value of called function
	sw $s0, 12($sp)
	j label5
label5:
	j epilogue_main

# Epilogue begins
epilogue_main:
	add $sp, $sp, 24
	lw $fp, -4($sp)
	lw $ra, 0($sp)
	jr $ra	# Jump back to the called procedure
# Epilogue ends
