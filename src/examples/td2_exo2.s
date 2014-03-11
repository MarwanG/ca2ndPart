	.text
	.ent main
main:	
	lw $1, 0($15)
	addi $2, $1, 4
	sw $2, 4($15)
	lw $3, 8($15)
	mult $4, $3, $2
	lw $1, 12($15)
	add $5, $1, $3
	sw $5, 16($15)
	lw $6, 20($15)
	mult $7, $5, $6
	sw $7, 24($15)
	j $31
	nop
	
	.end main

