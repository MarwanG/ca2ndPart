	.text
	.ent main
main:	
	lw $4, 0($2)
	addi $5, $4, 10
	add $4, $11, $8
	xor $8, $5, $4
	sw $8, 0($3)
	sw $8, 4($3)
	addi $2, $2, 10
	
	.end main