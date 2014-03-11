	.text
	.ent main
main:	
	lw $4, 0($6)
	add $5,	$4, $2
	sw $5, 0($6)
	bne $5, $0, $L5
	add $0, $0, $0
	
	sub $6, $0, $5
	sll $6, $3, 4
	addiu $5, $6, -2
	sw $5, 12($7)	
	sw $10, -4($6)

$L5:
	sub $8, $10, $5 	
	sll $10, $10, 4	
	sw $8, 8($7)	
	add $10, $8, $10	
	sw $10, 12($7)
	
	.end main

