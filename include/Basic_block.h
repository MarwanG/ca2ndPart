#ifndef _Basic_block_H
#define _Basic_block_H

/**	\file	Basic_block.h
	\brief	Basic_block class
	\author	Hajjem
*/


#include <Node.h>
#include <Instruction.h>
#include <string>
#include <stdio.h>
#include <Enum_type.h>
#include <fstream>
#include <list>
#include <Dfg.h>
#include <Node_dfg.h>

class Node_dfg;


/**	\class	Basic_block
	\brief	class representing a Basic_block of a fonction
*/

class Basic_block{

public:
   
   static void show_dependances(Instruction*, Instruction*);

/**	\brief	Constructor of a Basic Block
 */
   Basic_block();

/**	\brief	Destructor of a basic block
 */
   ~Basic_block();

   
/**	\brief	setter of the head of the basic block
 */
   void set_head(Node *);

/**	\brief	setter of the end of the basic block
 */
   void set_end(Node *);

/**	\brief	get the head of the basic block
 */
   Node* get_head();

/**	\brief	get the end of the basic block
 */
   Node* get_end();

/**	\brief	setter of Node corresponding to the branch
 */
   void set_branch(Node *);

/**	\brief	get the Node corresponding to the branch
 */
   Node* get_branch();

/**	\brief	Return true if the first line of the block is a label
 */
   bool is_labeled();

/**	\brief	set the index of the basic block
 */
   void set_index(int i);

/**	\brief	get the index of the basic block
 */
   int get_index();


/**	\brief	returns the size (in nodes) of the basic block
 */
   int size();	


/**	\brief	returns/gets the number of successors of the basic block
 */
   int get_nb_succ();

/**	\brief	returns/gets the number of predecessors of the basic block
 */
   int get_nb_pred();

/**	\brief	setter of the successor of the basic block
 */
   void set_successor1(Basic_block *BB);

/**	\brief	get the successor of the basic block
 */
   Basic_block *get_successor1();

/**	\brief	setter of the successor of the basic block
 */
   void set_successor2(Basic_block *BB);

/**	\brief	get the successor of the basic block
 */
   Basic_block *get_successor2();

/**	\brief	setter of the predecessor of the basic block
 */
   void set_predecessor(Basic_block *BB);

/**	\brief	get the ith predecessor of the basic block
 */
   Basic_block *get_predecessor(int );



/**	\brief	returns the number of instructions
 */

   int get_nb_inst();

   Node* get_first_node_instruction();
/**	\brief return the first instruction of the basic block, NULL if any
 */
   Instruction* get_first_instruction();
   Instruction* get_last_instruction();

/**	\brief	returns the instruction at the given index, NULL if any
 */
   Instruction* get_instruction_at_index(int);

/**	\brief	link instructions in the order they appear in the code
 */
   void link_instructions();

/**	\brief	computes dependances predecessors and successors of each instructions in the BB
 */
   void comput_pred_succ_dep();


/**	\brief	to display the basic block
 */
   void display();


/**	\brief	restitutes the basic block in a file
 */
   void restitution(string const);	

/**     \brief sets the parameter as successor and this as predecessor of the parameter
 */
   void set_link_succ_pred(Basic_block*);


/**	\brief	tests if the instruction is in the delayed slots of the branch terminating the BB if any
*/
   bool is_delayed_slot(Instruction*);	
   
  
 /**	\brief	gives the number of cycles to execute all instruction in this
*/  
   int nb_cycles();
   
   
/**	\brief	this method is to be used to test other methods
 */
   void test();
   
#define NB_REGISTRES 32

private:
   
   typedef struct{
      OPRegister *def;
      list <OPRegister*> uses;
   }def_use_t;
   
   Node *_head;
   Node *_end;

   Instruction *_firstInst;
   Instruction *_lastInst;

   Node *_branch;

   int _index;
   int _nb_instr;
   
   list <Basic_block *> _succ;
   list <Basic_block *> _pred;
   list <Basic_block *> _dom;
   list <Basic_block *> _pdom;
   
   list<def_use_t *>* _defs_uses[NB_REGISTRES];
   
   
};

#endif
