#include <Node.h>

Node::Node(Line * content){
	_content= content;
	_next=NULL;
	_prev=NULL;
}

Node::~Node(){
}

Node* Node::get_next(){
   return _next;
}

void Node::set_next(Node *newsuccessor){
   _next=newsuccessor;
}

Node* Node::get_prev(){
   return _prev;
}

void Node::set_prev(Node *newprev){
   _prev=newprev;
}
	
	
string Node::get_lineContent(){
  return _content->get_content();
}

Line* Node::get_line(){
	return _content;
}
	
void Node::set_line(Line * newline){
	_content=newline;
}
