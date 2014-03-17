#include <Function.h>

Function::Function(){
  _head = NULL;
  _end = NULL;
}

Function::~Function(){}

void Function::set_head(Node *head){
  _head = head;
}

void Function::set_end(Node *end){
  _end = end;
}

Node* Function::get_head(){
  return _head;
}

Basic_block* Function::get_firstBB(){
   return _myBB.front();
}

Node* Function::get_end(){
  return _end;
}
void Function::display(){
  cout<<"Begin Function"<<endl;
  Node* element = _head;

  if(element == _end)	
    cout << _head->get_lineContent() <<endl;

  while(element != _end){
    cout << element->get_lineContent() <<endl;
		
    if(element->get_next()==_end){
      cout << element->get_next()->get_lineContent() <<endl;
      break;
    }
    else element = element->get_next();

    }
  cout<<"End Function\n\n"<<endl;
	
}

int Function::size(){
  Node* element = _head;
  int lenght=0;
  while(element != _end)
    {
      lenght++;		
      if (element->get_next()==_end)
	break;
      else
	element = element->get_next();
    }
  return lenght;
}	


void Function::restitution(string const filename){
	
  Node* element = _head;
  ofstream monflux(filename.c_str(), ios::app);

  if(monflux){
    monflux<<"Begin"<<endl;
    if(element == _end)	
      monflux << _head->get_line()-> get_content() <<endl;
    while(element != _end)
      {
	if(element->get_line()->isInst() || 
	   element->get_line()->isDirective()) 
	  monflux<<"\t";
	
	monflux << element->get_lineContent() ;
	
	if(element->get_lineContent().compare("nop")) 
	  monflux<<endl;
		
	if(element->get_next()==_end){
	  if(element->get_next()->get_line()->isInst() || 
	     element->get_next()->get_line()->isDirective())
	    monflux<<"\t";
	  monflux << element->get_next()->get_lineContent()<<endl;
	  break;
	}
	else element = element->get_next();

      }
    monflux<<"End\n\n"<<endl;
		
  }

  else {
    cout<<"Error cannot open the file"<<endl;
  }

  monflux.close();
}

void Function::comput_label(){
  Node* element = _head;

  if(element == _end && element->get_line()->isLabel())	
    _list_lab.push_back(dynamic_cast< Label *> (element->get_line()));
  while(element != _end)
    {

      if(element->get_line()->isLabel())	
	_list_lab.push_back(dynamic_cast< Label * > (element->get_line()));

      if(element->get_next()==_end){
	if(element->get_line()->isLabel())	
	  _list_lab.push_back(dynamic_cast< Label * > (element->get_line()));
	break;
      }
      else element = element->get_next();

    }

}

int Function::nbr_label(){
  return _list_lab.size();

}

Label* Function::get_label(int index){

  list<Label*>::iterator it;
  it=_list_lab.begin();

  int size=(int) _list_lab.size();
  if(index< size){
    for (int i=0; i<index;i++ ) it++;
    return *it;	
  }
  else cout<<"Error get_label : index is bigger than the size of the list"<<endl; 
	
  return _list_lab.back();
}

Basic_block *Function::find_label_BB(OPLabel* label){
  //Basic_block *BB = new Basic_block();
   int size=(int)_myBB.size();
   string str;
   for(int i=0; i<size; i++){		
      if(get_BB(i)->is_labeled()){
	 
	 str=get_BB(i)->get_head()->get_lineContent();
	 if(!str.compare(0, (str.size()-1),label->get_op())){
	    return get_BB(i);
	 }
      }
  }
  return NULL;
}

//Calcule la liste des blocs de base : il faut délimiter les BB, en parcourant la liste des lignes/instructions à partir de la premiere, il faut s'arreter à chaque branchement (et prendre en compte le delayed slot qui appartient au meme BB, c'est l'instruction qui suit tout branchement) car il indique la fin d'un BB/une entete qui est l'instruction qui suit l'instruction du delayed slot ou à chaque label (on estime que tout label est utilisé par un saut et donc un label correspond correspond à une entete de BB).
//exemple 
/*
etiq:  <- etiquette => prochaine instruction est une entete
   i1
   i2
   i3
   saut
   i4   <- appartient au même BB que 'saut'
   i5   <- i5 est une entete
   ...

*/ 

void Function::add_BB(Node *debut, Node* fin, int index){
   Basic_block *b=new Basic_block();
   b->set_head(debut);
   b->set_end(fin);
   b->set_index(index);
   _myBB.push_back(b);
}

void Function::comput_basic_block(){
   Node *debut, *current, *prev;
   current=_head->get_next()->get_next();
   debut= NULL;
   prev = NULL;
   int ind=0;
   Line *l=NULL;
   Instruction *i=NULL;
   
   cout<< "comput BB" <<endl;
   cout<<"head :"<<_head->get_lineContent()<<endl;
   cout<<"tail :"<<_end->get_lineContent()<<endl;
   
   while(current != NULL && current!=_end){
      if((current->get_line()->isInst())||(current->get_line()->isLabel())){
        if(debut == NULL){
          debut = current;
        }else if (current->get_line()->get_content()=="add $0,$0,$0"){
          cout<<"-- Bloc numero:"<<ind<<endl;
          cout<<"-- head :"<< debut->get_lineContent()<<endl;
          cout<<"-- end :"<<current->get_lineContent()<<endl;
          add_BB(debut,current,ind);
          get_BB(nbr_BB()-1)->set_branch(prev);
          ind++;
          debut = NULL;
       }else if(current->get_next()->get_line()->isLabel()){
          cout<<"-- Bloc numero:"<<ind<<endl;
          cout<<"-- head :"<< debut->get_lineContent()<<endl;
          cout<<"-- end :"<<current->get_lineContent()<<endl;
          add_BB(debut,current,ind);
          ind++;
          debut = current->get_next();
        }
      }
    prev = current;
    current = current->get_next();
  }
  cout<<"end comput BB"<<endl;
}

int Function::nbr_BB(){
   return _myBB.size();
}

Basic_block *Function::get_BB(int index){

  list<Basic_block*>::iterator it;
  it=_myBB.begin();
  int size=(int)_myBB.size();

  if(index< size){
    for (int i=0; i<index;i++ ) it++;
    return *it;	
  }
  else 
    return NULL;
}

list<Basic_block*>::iterator Function::bb_list_begin(){
   return _myBB.begin();
}

list<Basic_block*>::iterator Function::bb_list_end(){
   return _myBB.end();
}

/* comput_pred_succ calcule les successeurs et prédécesseur des BB, pour cela il faut commencer par les successeurs */
/* et itérer sur tous les BB d'une fonction */
/* il faut determiner si un BB a un ou deux successeurs : dépend de si le BB termine avec un saut */
/* si pas de saut ou si saut incontionnel : 1 successeur */
/* si branchement conditionnel : 2 successeurs, il faut trouver le BB cible de saut à partir de l'etiquette */ 


// NB : penser  utiliser la méthode set_link_succ_pred(Basic_block *) de la classe Basic_block  
void Function::comput_succ_pred_BB(){
  
   list<Basic_block*>::iterator it, it2;
   Basic_block *current;
   Instruction *instr;
   int nbi;
   Operand* op;
   
   Basic_block *succ=NULL;
   
   int size= (int) _myBB.size(); // nombre de BB
   it=_myBB.begin();   //1er BB
   //remarque : le dernier block n'a pas de successeurs
  

   

  for(nbi = 0; nbi < nbr_BB(); nbi++){
    current = get_BB(nbi);
    instr = current->get_last_instruction();
    if(instr->get_content()=="add $0,$0,$0"){  //ilya un jump
      instr = instr->get_prev();
      if(instr->get_content().at(0)=='j'){    //check if we use jr .. etc
        string label = instr->get_op1()->to_string();
        Basic_block * suc  = find_label_BB(new OPLabel(label));
        current->set_successor1(suc);
      }else{
        int nb = instr->get_nbOp();
        if(nb == 2){
          string label = instr->get_op2()->to_string();
          Basic_block * suc  = find_label_BB(new OPLabel(label));
          current->set_link_succ_pred(suc);           
        }else{
          string label = instr->get_op3()->to_string();  //egal a 3.
          Basic_block * suc  = find_label_BB(new OPLabel(label));
          current->set_link_succ_pred(suc);          
        }
        current->set_link_succ_pred(get_BB(nbi+1));          
      }
    }else{
        current->set_link_succ_pred(get_BB(nbi+1));
    }    
  }



   //A REMPLIR


}




/* en implementant la fonction test de la classe BB, permet de tester des choses sur tous les blocs de base d'une fonction par exemple l'affichage de tous les BB d'une fonction ou l'affichage des succ/pred des BBs comme c'est le cas -- voir la classe Basic_block et la méthode test */

void Function::test(){
   int size=(int)_myBB.size();
   for(int i=0;i<size; i++){
    get_BB(i)->test();
  }
}
