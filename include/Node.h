#ifndef _Node_H
#define _Node_H

/**	\file	Node.h
	\brief	Node class
	\author	Hajjem
*/


#include <Line.h>
#include <string>
#include <Enum_type.h>
using namespace std;

/**	\class	Node
	\brief	class representing a Node in list
*/

class Node{

public:

/**	\brief	Node constructor
*/
	Node(Line * content);
	
/**	\brief	Node destructor
*/
	~Node();

/**	\brief	get the next node
*/
	Node * get_next();
	
/**	\brief	set the next node
*/
	void set_next(Node*);

/**	\brief	get the previous node
*/
	Node * get_prev();
	
/**	\brief	set the previous node
*/
	void set_prev(Node*);
	
/**	\brief	get the current line
*/
	Line * get_line();

/**	\brief	set the current line
*/
	void set_line(Line * newline);

/**	\brief	get the content of the line
*/
	string get_lineContent();
private:
	Node * _next;
	Node * _prev;
	Line * _content;
	
};

#endif
