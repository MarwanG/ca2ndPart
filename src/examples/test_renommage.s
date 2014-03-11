	.text
	.ent main
main:	
	add $4, $3, $2
	sw $4, 0($30)
	add $4, $6, $7
	j $31
	nop
	
	.end main

