#ifndef _Node_dfg_H
#define _Node_dfg_H

/**	\file	Node_dfg.h
	\brief	Node_dfg class
	\author	Hajjem
*/



#include <Basic_block.h>
#include <string>
#include <stdio.h>
#include <Label.h>
#include <Enum_type.h>

class Node_dfg;

using namespace std;

/**	\class	Node_dfg
	\brief	class representing a node of data flow graph
*/

typedef struct{
	int delai;
	t_Dep dep;
	Node_dfg *next;
}Arc_t;

class Node_dfg{

public:

/**	\brief	Constructor of Node_dfg
*/
	Node_dfg(Instruction*);

/**	\brief	Destructor of Node_dfg
*/
	~Node_dfg();

/**	\brief	get the ith arc of the arc list
*/
	Arc_t *get_arc(int i);


	list<Arc_t*>::iterator arcs_begin();
	list<Arc_t*>::iterator arcs_end();


/**	\brief	get the number of arcs
*/
	int get_nb_arcs();

/**	\brief	get the Instruction
*/
	Instruction *get_instruction();

/**	\brief	add an arc to the arc list
*/
	void add_arc(Arc_t*);

	void add_predecesseur(Node_dfg*);
	int nb_preds();
	list<Node_dfg*>::iterator pred_begin();
	list<Node_dfg*>::iterator pred_end();

/**	\brief	set the Instruction
*/
	void set_instruction( Instruction* );

	

/**	\brief	set the weight
*/
	void set_weight( int );

/**	\brief	get the weight
*/
	int get_weight( );



/**	\brief	set the number of descendant
 */
	void set_nb_descendant(int);

/**	\brief	get the number of descendant
*/
	int get_nb_descendant();
/**  
 	\brief	set tready to t
*/
	void set_tready(int t);

/**  
 	\brief	returns tready 
*/
	int get_tready();


private:
	list <Arc_t *> _arc;
	list <Node_dfg *> _pred; //liste des noeuds predecesseurs
	Instruction * _inst; // instruction correspondante
	int _nbr_descendant; // nombre de descendants
	int _poids;   // poids dans le chemin critique
	int _tready;  
	
};



#endif
