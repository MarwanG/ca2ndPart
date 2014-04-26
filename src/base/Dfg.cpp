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

   nodel = list_node_dfg.begin();
   for(int i =  0 ; i < _length ; i++){
      Node_dfg * nd =  *nodel;
      Instruction * inst = nd->get_instruction();
      if(inst->get_nb_pred() == 0 && !inst->is_branch()) {
       _roots.push_back(nd);
      }
      if(inst->is_branch()) {
      _delayed_slot.push_back(*(++nodel));
      break;
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
         Arc_t * arc = new_arc(delay,(*it)->type,succ);
         nd->add_arc(arc);
         it++;
      }
      nodel++;
   }

}


list<Node_dfg*> Dfg::get_inverse_topologic_order() {
  list<Node_dfg*> l, r;//r = liste résultat
  list<Node_dfg*>::iterator it;

  for(it=list_node_dfg.begin();it!=list_node_dfg.end();it++) {
    if((*it)->get_nb_arcs() == 0){
      r.push_back(*it);
      l.push_back(*it);
      _read[(*it)->get_instruction()->get_index()] = 1;
    } else {
      _read[(*it)->get_instruction()->get_index()] = 0;
    }
  }

  while(!l.empty()){
    Node_dfg* candidat = l.front();
    l.pop_front();
    bool succ_treated = true;
    list<Arc_t*>::iterator it_succ;
    for(it_succ=candidat->arcs_begin();it_succ!=candidat->arcs_end();it_succ++){
      succ_treated &= (_read[(*it_succ)->next->get_instruction()->get_index()]==1);
      if(!succ_treated){
   l.push_front(candidat);
   l.push_front((*it_succ)->next);
   break;
      }
    }
    if(succ_treated){
      if( _read[candidat->get_instruction()->get_index()]!=1){
   r.push_back(candidat);
   _read[candidat->get_instruction()->get_index()]=1;
      }
      list<Node_dfg*>::iterator preds;
      for(preds=candidat->pred_begin();preds!=candidat->pred_end();preds++)
   if(_read[(*preds)->get_instruction()->get_index()]==0)
     l.push_back(*preds);
    }
  }

  return r;
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


bool Dfg::contains(list<Node_dfg*>* l, Node_dfg* n){
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
   list<Node_dfg*>::iterator listNode;
   list<Node_dfg*> list_node_ordered = get_inverse_topologic_order();


   for(listNode=list_node_dfg.begin();listNode!=list_node_dfg.end();listNode++)
    (*listNode)->set_weight(0);

   for(listNode=list_node_ordered.begin();listNode!=list_node_ordered.end();listNode++){
   Node_dfg * tmp = *listNode;
    if(tmp->get_nb_arcs() == 0)
      tmp->set_weight(tmp->get_instruction()->get_latency());
    else {
      list<Arc_t*>::iterator it_succ;
      for(it_succ=tmp->arcs_begin();it_succ!=tmp->arcs_end();it_succ++)
          (*listNode)->set_weight(max((*listNode)->get_weight(),(*it_succ)->delai+(*it_succ)->next->get_weight()));
      }
  }




#ifdef DEBUG
  it=list_node_dfg.begin();
  for(unsigned int k = 0; k < list_node_dfg.size(); k++, it++){
    Node_dfg* node = *it;
    cout << "node inst " << node -> get_instruction() -> get_index() << " poids=" << node->get_weight() << " nb succ=" << node->get_nbr_arc() << endl;
  }
#endif
}



// A FAIRE
int Dfg::get_critical_path(){
  list<Node_dfg*>::iterator listNode;
  comput_critical_path();
  int criticalpath =0;
  for(listNode=_roots.begin();listNode!=_roots.end();listNode++)
    criticalpath = max(criticalpath,(*listNode)->get_weight());

  return criticalpath;
}


bool Dfg::willFreeze(Node_dfg* node){
  list <Node_dfg*>::iterator listNode = new_order.begin();
  int i, n;
  n = new_order.size();
  for(i=0;i<n;i++){
    if (contains(node->get_pred(),*listNode)) {
      Instruction *pred = (*listNode)->get_instruction();
      Instruction *succ = node->get_instruction();
      if (get_delay(pred->is_dependant(succ),pred,succ) > n - i) {
          return true;
      }
    }
    listNode++;
  }
  return false;
}

bool compare_weight(Node_dfg* a, Node_dfg* b){
  return a->get_weight() > b->get_weight();
}

bool Dfg::compare_freeze(Node_dfg* a, Node_dfg* b){
  if(willFreeze(a))
    return !willFreeze(b);
  else
    return true;
}
bool compare_desc(Node_dfg* a, Node_dfg* b){
  return a->get_nb_descendant() > b->get_nb_descendant();
}
bool compare_pred(Node_dfg* a, Node_dfg* b){
  return a->nb_preds() > b->nb_preds();
}
bool compare_latency(Node_dfg* a, Node_dfg* b){
  return a->get_instruction()->get_latency() > b->get_instruction()->get_latency();
}
bool compare_index(Node_dfg* a, Node_dfg* b){
  return a->get_instruction()->get_index() < b->get_instruction()->get_index();
}







void Dfg::sortList(list<Node_dfg*>* l){  
  l->sort(compare_index);
  l->sort(compare_desc);
  l->sort(compare_pred);
  l->sort(compare_latency);
  l->sort(compare_weight);
  list<Node_dfg*>::iterator iti, itj;
  for(iti=l->begin();iti!=l->end();iti++)
    for(itj=iti;itj!=l->end();itj++)
      if(willFreeze(*iti))
   if(!willFreeze(*itj)){
     std::swap(*iti, *itj);
     break;
   }
}


bool Dfg::isReady(Node_dfg * n){
   list<Node_dfg*>::iterator pred;
   pred = n->pred_begin();
   for(int i = 0 ; i < n->nb_preds() ; i++){
      if(!(contains(&_inst_ready,*pred)) && !contains(&new_order,*pred)){
         return false;
      }
      pred++;
   }
   return true;
}


void  Dfg::scheduling(){
  
  list <Node_dfg*>::iterator listNode;
  Node_dfg * NodeTmp ;


  for(listNode=_roots.begin();listNode!=_roots.end();listNode++){
   // if(!contains(&_inst_ready,*listNode)){
      _inst_ready.push_back(*listNode); 
   // }
  }
  while(_inst_ready.size() > 0){
    sortList(&_inst_ready);
    Node_dfg * tmp = _inst_ready.front();
    _inst_ready.pop_front();
    new_order.push_back(tmp);
    list <Arc_t *> ::iterator listArc;
    listArc = tmp->arcs_begin();
    for(int i = 0 ; i < tmp->get_nb_arcs() ; i++){
      NodeTmp = (*listArc)->next;
      //if(isReady(NodeTmp)){
        // _inst_ready.push_back(NodeTmp);    MON IF QUI MARCHE PAS
      //}
      if(!contains(&new_order,(*listArc)->next) && !contains(&_inst_ready,(*listArc)->next))
         _inst_ready.push_back((*listArc)->next);
      listArc++;
    }
    
  }


}

void Dfg::display_sheduled_instr(){
   list <Node_dfg*>::iterator it;
   Instruction *inst;
   for(it=new_order.begin(); it!=new_order.end(); it++){
      inst=(*it)->get_instruction();
      cout<<"i"<<inst->get_index()<<": "<<inst->get_content()<<endl;
   }
}
