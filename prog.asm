.text
.globl main
main:
  move $fp, $sp
  addi $fp, $sp, -4
_add:
  lw $t0, 0($sp)
  lw $t1, 4($sp)
  add $v0, $t0, $t1
  jr $ra
_sub:
  lw $t0, 0($sp)
  lw $t1, 4($sp)
  sub $v0, $t0, $t1
  jr $ra
_mul:
  lw $t0, 0($sp)
  lw $t1, 4($sp)
  mul $v0, $t0, $t1
  jr $ra
_div:
  lw $t0, 0($sp)
  lw $t1, 4($sp)
  div $v0, $t0, $t1
  jr $ra
_eq:
  lw $t0, 0($sp)
  lw $t1, 4($sp)
  beq $t0, $t1, equal
  li $v0, 0
  jr $ra
equal:
  li $v0, 1
  jr $ra
_neq:
  lw $t0, 0($sp)
  lw $t1, 4($sp)
  beq $t0, $t1, notequal
  li $v0, 0
  jr $ra
notequal:
  li $v0, 1
  jr $ra
  lw $v0, 0($fp)
  beqz $v0, l1
  li $v0, 2
  sw $v0, 0($fp)
  jal l2
l1:
  li $v0, 0
  sw $v0, 0($fp)
  lw $v0, 0($fp)
  move $sp, $fp
  jr $ra
l2:
  move $a0, $v0
  li $v0, 1
  syscall
  jr $ra

.data
