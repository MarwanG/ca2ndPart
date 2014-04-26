#include <Dfg.h>

// crée un arc et le renvoie
Arc_t* new_arc(int del, t_Dep d, Node_dfg *n){
   Arc_t *arc = new Arc_t;
   arc->delai=del;
   arc->dep=d;
   arc->next=n;
   
   return arc;
}

//rend le delay entre 2 instructions pour la dépendance donnée
int get_delay(t_Dep dep, Instruction *from, Instruction *to){
   switch(dep){
   case WAW:
      return WAW_DELAY;
   case WAR:
      return WAR_DELAY;
   case MEMDEP:
      return MEMDEP_DELAY;
   case CONTROL:
      return 0;
   case NONE:
      return 0;
   case RAW:
      int ret=t_delay[from->get_type()][to->get_type()];
      if(ret<1)
	 return 1;
      return ret;
   }
   
   return 0;
}

// A REMPLIR
Dfg::Dfg(Basic_block *bb){
   cout << "doing the dfg" << endl;
   list<Arc_t*>::iterator ita;
   list<Node_dfg*>::iterator nodel;
   list<Node_dfg*>::iterator tmp;
   list<int>::iterator listN;  
 
   _bb=bb;
   _index_branch=-1;
   _nb_arc=0;  
   _length=bb->get_nb_inst();
   _read= new int[_length];
   
   bb->comput_pred_succ_dep();
   Node_dfg* branch = NULL;
   

   for(int i = 0 ; i < _length ; i++){
      Node_dfg * nd = new Node_dfg(_bb->get_instruction_at_index(i));
      if(nd->get_instruction()->is_branch()){
         branch = nd;
      }
      list_node_dfg.push_back(nd);
   }

   
   // A COMPLETER
   nodel = list_node_dfg.begin();
   for(int i =  0 ; i < _length ; i++){
      Node_dfg * nd =  *nodel;
      Instruction * inst = nd->get_instruction();
      inst->print_succ_dep();
      if(inst->get_nb_pred() == 0 && !inst->is_branch()) {
       _roots.push_back(nd);
      }
      if(inst->is_branch()) {
      _delayed_slot.push_back(*(++nodel));
      break;
      }
      if(inst->get_nb_pred() == 0 && !inst->is_branch()) {
         _roots.push_back(nd);
      }
       if(inst->succ_begin()==inst->succ_end() && branch){
         Arc_t* arc_branch = new_arc(0,CONTROL,branch);
         nd->add_arc(arc_branch);
         branch->add_predecesseur(nd);
         _nb_arc++;
       } 
      list<dep*>::iterator it;
      it = inst->succ_begin();
      for(int j = 0 ; j < inst->get_nb_succ() ; j++){
         int nbDFG =  (*it)->inst->get_index();
         tmp = list_node_dfg.begin();
         std::advance(tmp, nbDFG);
         Node_dfg * succ = *tmp;
         succ->add_predecesseur(nd);
         int delay = get_delay((*it)->type,inst,succ->get_instruction());
         cout << delay << endl;
         Arc_t * arc = new_arc(delay,(*it)->type,succ);
         nd->add_arc(arc);
         it++;
      }
      nodel++;
   }

}



// methode auxiliaire pour la construction du Dfg, pas forcément utile, dépend de comment vous envisagez de faire...
void Dfg::build_dfg(Node_dfg*,bool) {

  // A REMPLIR OU NON !
 return;
}

Dfg::~Dfg(){}


void Dfg::display(Node_dfg * node, bool first){
   
   
   list<Node_dfg*>::iterator it;
   it=_roots.begin();

   if(first)	
      for(int i=0; i<_length; i++)	
	 _read[i]=0;  	
   
   for (unsigned int j=0; j<_roots.size();j++ ){ 
      if(first) node = *it;	
			

      if(!_read[node->get_instruction()->get_index()]){
	 _read[node->get_instruction()->get_index()]=1;
	 cout<<"pour i"<<node->get_instruction()->get_index()<<endl;
	 cout<<"l'instruction "<<node->get_instruction()->get_content()<<endl;
			
	 //On affiche ses successeurs s'il en a
	 for(int i=0;i<node->get_nb_arcs();i++){
	    if (node->get_arc(i)){
	       cout<< " -> succ i"
		   << node->get_arc(i)->next->get_instruction()->get_index()
		   << " : "
		   << node->get_arc(i)->next->get_instruction()->get_content()
		   << endl;
	    }
	 }
	 for(int i=0;i<node->get_nb_arcs();i++){
	    if (node->get_arc(i))
	       display(node->get_arc(i)->next, false);
	 }
      }
      it++;

   }
}

#define DEP(x) ((x==NONE)?"":((x==RAW)?"raw":\
				   ((x==WAR)?"war":\
				    ((x==WAW)?"waw": \
				     ((x==MEMDEP)?"mem": "control")))))


//Pour générer le fichier .dot: dot -Tps graph.dot -o graph.ps
void Dfg::restitute(Node_dfg * node, string const filename, bool first){
   if(first)
      remove(filename.c_str());
   ofstream monflux(filename.c_str(), ios::app);
   list<Node_dfg*>::iterator it;
 
   if(first && _length){
     
      for(int i=0; i<_length; i++)
	 _read[i]=0;
      
      it = _delayed_slot.begin();
      
      int index_min = _length;
      
      for(unsigned int i=0; i < _delayed_slot.size(); i++){
	 _read[(*it)->get_instruction()->get_index()] = 1;
	 if (index_min > (*it)->get_instruction()->get_index())
	    index_min = (*it)->get_instruction()->get_index();
	 it++;
      }

      monflux<<"digraph G1 {"<<endl;
      for(int i=0; i<index_min; i++){
	 monflux<<"i"<<i<< ";"<<endl;
	 
      }
   }	
   it=_roots.begin();
   for (unsigned int j=0; j<_roots.size();j++ ){ 		

      if(first) node = *it;
		
      if(monflux){			
	 //monflux.open(filename.c_str(), ios::app);
	 if(!_read[node->get_instruction()->get_index()]){
	    _read[node->get_instruction()->get_index()]=1;
					
	    //On affiche ses successeurs s'il en a
	    for(int i=0; i<node->get_nb_arcs(); i++){
	       if (node->get_arc(i)){
	   
		  monflux<<"i"<<node->get_instruction()->get_index();
		  monflux<<" ->  i" << node->get_arc(i)->next->get_instruction()->get_index();

		  // monflux<<"i"<<node->get_instruction()->get_index()<<"_"<<node->get_weight();
		  // monflux<<" ->  i" << node->get_arc(i)->next->get_instruction()->get_index();
		  // monflux<<"_"<<node->get_arc(i)->next->get_weight();

		  monflux<<" [label= \""<< DEP(node->get_arc(i)->dep) << node->get_arc(i)->delai<<"\"];"<<endl;
	       }
	    }
	    monflux.close();
	
	    for(int i=0;i<node->get_nb_arcs();i++){
	       if (node->get_arc(i))
		  restitute(node->get_arc(i)->next,filename.c_str(),false);	
	    }
	 }
      }
      if((j+1) < _roots.size())	monflux.open(filename.c_str(), ios::app);
      it++;
   }

   if (first && _length){
      monflux.open(filename.c_str(), ios::app);
      monflux<<"}"<<endl;
      monflux.close();
   }
   return;
 
}

bool Dfg::read_test(){
  for(int i=0; i<_length; i++)	if(_read[i]==0)	return true;
  return false;
}


bool contains(list<Node_dfg*>* l, Node_dfg* n){
   list<Node_dfg*>::iterator it;
   
   for(it=l->begin(); it!= l->end(); it++){
      if( (*it)==n ){
	 return true;
      }
   }
   return false;
}

//A FAIRE
void Dfg::comput_critical_path(){



#ifdef DEBUG
  it=list_node_dfg.begin();
  for(unsigned int k = 0; k < list_node_dfg.size(); k++, it++){
    Node_dfg* node = *it;
    cout << "node inst " << node -> get_instruction() -> get_index() << " poids=" << node->get_weight() << " nb succ=" << node->get_nbr_arc() << endl;
  }
#endif
}



// A FAIRE
int Dfg::get_critical_path(){}














//
//void  Dfg::scheduling(){
//}

void Dfg::display_sheduled_instr(){
   list <Node_dfg*>::iterator it;
   Instruction *inst;
   for(it=new_order.begin(); it!=new_order.end(); it++){
      inst=(*it)->get_instruction();
      cout<<"i"<<inst->get_index()<<": "<<inst->get_content()<<endl;
   }
}
