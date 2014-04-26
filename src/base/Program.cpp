#include <Program.h>
#include <asm_mipsyac.h>

extern	void programparse(string) ; 
extern	Program prog ;

Program::Program(){
   _head= NULL;
   _length=0;
}


//constructeur de copie
Program::Program(Program const&  otherprogram){
   //On initialise la liste.
   _head= NULL;
   _length= 0;
   // On copie la liste.
   Node * tmp = otherprogram._head;
   while (tmp != NULL){
      add_line(tmp->get_line());
      tmp = tmp->get_next();
   }
}

//constructeur qui vas permettre de parser un fichier
Program::Program (string const file){
   _head = NULL ;
   _length = 0 ;
   programparse(file) ;
  
   Node * tmp = prog._head;
   while (tmp != NULL){
      add_line(tmp->get_line());
      tmp = tmp->get_next();
   }
}

Program::~Program(){
   delete _head;
   _head=NULL;
   _length=0;
}



void Program::add_line(Line * newline){
   Node *nod = new Node(newline);
   if(!_head){
      _head= nod;
      _end=nod;
   }
   else{
      nod->set_prev(_end);
      _end->set_next(nod);
      _end=nod;
   }
   _length++;
}


void Program::del_line(int index){
   Node * to_delete;
   Node * prec;
	
   if (index >= 0 && index < _length){
      if (index == 0){
	 if (_length > 0){
	    // On efface le maillon.
	    to_delete = _head;
	    _head = _head->get_next();	
	    _head->set_prev(NULL);
	 }
      }
      else {	// On se place sur le precedent.
	 prec = _head;
	 for (int i = 0; i < index-1; ++i){
	    prec = prec->get_next();
	 }

	 // On retire le maillon.
	 to_delete = prec->get_next();
	 prec->set_next( to_delete->get_next() );
	    
      }
      delete to_delete;
      --_length;
   }
}

int Program::add_line_at(Line *newline, int position)
{
   if (position <= 0){
      Node * new_nod = new Node(newline);

      if (new_nod == NULL)  // Y avait-il assez de mÃ©moire ?
	 return 0;

      new_nod->set_next(_head);// new_nod pointe sur le premier.
      _head->set_prev(new_nod);
      new_nod->set_prev(NULL);  
      _head = new_nod;         // new_nod est maintenant premier.
      ++_length;
      return 1;
   }

   else if (position >= _length)
      add_line(newline);

   else
   {
      Node * new_nod = new Node(newline);
      Node * prec = _head;
      if (new_nod == NULL)// Y avait-il assez de memoire?
	 return 0;

      // On se place sur le precedent.
      for (int i = 0; i < position - 1; ++i){
	 prec = prec->get_next();
      }

      // On ajuste les pointeurs.
      new_nod->set_next(prec->get_next());
      prec->get_next()->set_prev(new_nod);
      prec->set_next(new_nod);
      new_nod->set_prev(prec);
      ++_length;
      return 1;
   }
   return 1;
}


void Program::display()
{
   Node* element = _head;
   while(element != NULL){
      cout << element->get_line()-> get_content() <<endl;
		
      if(element->get_next()==NULL)	
	 break;
      else 
	 element = element->get_next();
   }
   if (is_empty())	
      cout<<"The program is empty"<<endl;
   cout << endl;
}

void Program::flush(){

   while(!is_empty()){
      del_line(0);		
   }
}


void Program::exchange_line(int line1, int line2){
   Line * lg1,*lg2;
	
   lg1=find_line(line1);
   lg2=find_line(line2);

   del_line(line1);
   add_line_at(lg2,line1);
   del_line(line2);
   add_line_at(lg1,line2);
	
}

Line* Program::find_line(int index){
   int j;
   Node *e = _head;
   for (j=0; j< _length ;j++) {
      if(j==index) {
	 return e->get_line();
      }
      e = e->get_next();
   }
   return NULL;
}


int Program::size(){
   return _length;
}

bool Program::is_empty(){
   if(!_head)	
      return true;
   return false;
}

void Program::in_file(string const filename){
   Node* element = _head;
   ofstream monflux(filename.c_str());
  
   if(monflux){
      while(element != NULL)
      {
	 if(element->get_line()->type_line()==line_Instru || 
	    element->get_line()->type_line()== line_Direct) 
	    monflux<<"\t";
	 monflux << element->get_line()-> get_content();
	
	 if(element->get_next()==NULL)	
	    break;
	 else {
	    if(element->get_line()->get_content().compare("nop")) 
	       monflux<<endl;
	    element = element->get_next();
	 }			
      } 
   }
   else {
      cout<<"Error cannot open the file"<<endl;
   }
  
   monflux.close();	
}

/* Il faut ici délimite les fonctions du fichier assembleur en détectant les directives .ent et .end qui indique le début et la function d'une fonction 
Il faut donc parcourir toutes les lignes d'un programme et construire avec chaque couple de ligne comportant les directives .ent FCT et .end FCT une nouvelle fonction et l'ajouter à la liste des fonctions du programme

*/

/* NB : la méthode get_content() permet de récupérer une chaine de caractère correspondant au contenu d'une ligne/directive/label/instruction. Par exemple :

  string ma_chaine = ma_ligne->get_content();
/  On peut comparer ensuite si la chaine commencer par quelquechose avec : 
  if( ma_chaine.compare(0, 6, "coucou")==0){
	       //la chaine commence par "coucou"
               ....
	    }
*/

void Program::comput_function(){
  Node *element_debut=NULL;
   Node* current = _head;
   Line *l=NULL;
   Directive *d=NULL;
   string direct;
    Function * my_fct;
   
    while (current != NULL){

        Line *line = current->get_line();
        if(line->isDirective()){
            string s = line->get_content();
            if(s.compare(0,4,".ent")==0){
                my_fct = new Function();
                my_fct -> set_head(current);
            }
            else
              if(s.compare(0,4,".end")==0){
                my_fct -> set_end(current);
                  _myfunc.push_back(my_fct);
              }
        }
        current=current->get_next();
    }

   // A REMPLIR 
    
   if (is_empty())
      cout<<"The program is empty"<<endl;
}

int Program::nbr_func(){
   return _myfunc.size();
}

Function*  Program::get_function(int index){
   list<Function*>::iterator it;
   it=_myfunc.begin();
   int size=(int)_myfunc.size();
   if (index < size){
      for (int i = 0; i<index; i++) 
	 it++;
      return *it;	
   }
   return NULL;	
}

list<Function*>::iterator Program::function_list_begin(){
   return _myfunc.begin();
}

list<Function*>::iterator Program::function_list_end(){
   return _myfunc.end();
}


/* Pour chaque fonction du programme, donc de la liste _myfunc, il faut créer un CFG et l'ajouter à la liste _myCFG ;
   La création d'un CFG se fait avec un appel au constructeur, par exemple : 
   Cfg * cfg = new Cfg(bb0, n);
   crée un CFG dont le BB d'entrée est bb0 et contenant n BBs.
   Il faut avoir calculé les blocs de base des fonctions et les succ/pred des BB sinon le CFG n'aura qu'un bloc, le premier (meme si on dit qu'il en a n en paramètre)
*/

void  Program::comput_CFG(){
   list<Function*>::iterator it;
   Function *current;
   it=_myfunc.begin();
   Node* cur_line;
   int size=(int)_myfunc.size();
    
   for(int i=0; i<size; i++){ // parcours des functions du programme
      current=*it;
      
       current -> comput_basic_block(); 
      current -> comput_succ_pred_BB();
      Cfg * cfg = new Cfg(current->get_BB(0),current->nbr_BB());
      _myCFG.push_back(cfg);


      it++;
   }
   return;
}




Cfg*  Program::get_CFG(int index)
{
   list<Cfg*>::iterator it;
   it=_myCFG.begin();
   if (index< (int)_myCFG.size()){
      for (int i = 0; i<index;i++) 
	 it++;
      return *it;
       
   }
   return NULL;	
}
