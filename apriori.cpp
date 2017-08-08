/*
* Apriori Algorithm using hash tree for frequent itemset mining (data mining)
* Written by Mohammad Motallebi
* Implemented for CMPUT 690, Winter 2016
*/


#include <cmath>
#include <cstdio>
#include <iterator>
#include <fstream>
#include <unordered_map>
#include <set>
#include <vector>
#include <string>
#include <sstream>
#include <ctime>
using namespace std;

int global_subset_counter = 100;
vector<int> global_frequent_counter;// to keep number of frequent k_itemsets 

struct Frequent{
	vector<int> items;// items
	int count;// support
};

vector<vector<Frequent*>>* frequents;// to keep all frequent itemsets

struct Association{
	set<int>* left;// left side of the rule
	vector<int>* right;// right side o the rule
	float ratio;//confidence
	int count;//support
};

vector<Association> associations;// to keep all association rules

/*
* This corresponds to a node in the hash-tree that keeps the # of times it has been riched , and also
* it keeps its children (if any) on the map variable.
*/
struct my_struct{
	int count;
	unordered_map<int,my_struct*>* map;	
};

/*
* Given the name of the file containing transactions,
* this function returns a vector for every transaction,
* where items are pushed inside it.
*/
vector<vector<int>> create_ds(string file_name)
{
	ifstream infile(file_name);
	vector<vector<int>> transactions;
	string line;
	while(getline(infile, line))//read file line by line
	{
		istringstream iss(line);
		vector<string> tokens;
		copy(istream_iterator<string>(iss),
			istream_iterator<string>(),
			back_inserter(tokens));
		vector<int> transaction;
		for(int i=0;i<tokens.size();i++)
		{
			transaction.push_back(stoi(tokens[i]));
		}
		transactions.push_back(transaction);
	}
	return transactions;
}

/*
* This function recursively traverses the hash-tree and finds frequent itemset in different depths
* and adds them to the corresponding depth of the 'frequents' variable. The action is similar to DFS.
*/
void get_global_frequent( unordered_map<int, my_struct*>*& map, int depth, int min_support,vector<int> seen)
{
	for(auto it=map->begin();it!=map->end();it++)
	{
		if(it->second->count>=min_support)
		{
			global_frequent_counter[depth] +=1;
			seen.push_back(it->first);
			Frequent* f = new Frequent();
			f->count = it->second->count;
			f->items = vector<int>(seen.begin(),seen.end());
			(*frequents)[seen.size()].push_back(f);
			get_global_frequent(it->second->map,depth+1,  min_support,seen);
			seen.pop_back();
		}
	}
}

/*
* The main function that traverses the hash-tree
* given the current node, the ramaining items of the transaction( using a pointer and a size to speed up),
* k as the k-itemset, and min_support, based on the current depth (determined by k), does its job!
* if k=0 (ie leaf node) increases count for that leaf (or more accurately, the path it has traversed till now)
* else, (ie k>0), based on the count of the node, decides whether to continue or stop at that branch.
* The whole process is done for all remaining items of the transaction 
*/
void go_down(unordered_map<int,my_struct*>*& map, int* arr,const int& arr_size ,int k,const int& min_support)
{
	k--;
	if(k==0)// this is a leaf node
		for(register int i=0;i<arr_size;i++)// using register to speed up!
		{
			register auto t = map->find(arr[i]);
			if (t == map->end())//it doesn't exist, let's create it!
			{
				global_subset_counter++;
				my_struct* s = new my_struct();
				s->count = 1;
				s->map = new unordered_map<int,my_struct*>();
				(*map)[arr[i]] = s;
			}
			else// we already have it, lets increase the count;
			{
				t->second->count +=1;
			}
		}
	else// not a leaf node
		for(register int i=0;i<arr_size;i++)
		{
			if((*map)[arr[i]]->count<min_support)// this is not a leaf node and the count for it is less than min_support => do not continue!
			{
				continue;
			}
			else // internal node! and more than min_support, going down!
			{
				if(arr_size-i>1)
					go_down((*map)[arr[i]]->map,&arr[i+1],arr_size-i-1,k,min_support);
			}
		}
}

/*
* The main function that starts the apriori algorithm. It iterates till the algorithm cannot make further progress.
* At every iteration, by increasing k, the algorithm goes deeper to create k-itemsets.
* It retrieves transactions from DB and calls go-down function for every of them.
* At the time there is no more progress, it calls get_global_frequent to get all frequent itemsets.
*/
unordered_map<int, my_struct*>* run_A_priori(string file_name, int min_support, int max_item)
{
	int k = 0;// k-itemset
	unordered_map<int, my_struct*>* map = new unordered_map<int, my_struct*>();
	map->reserve(max_item);
	while(true)//iterating over k
	{
		k++;//starts from 1 and continues!;
		if(global_subset_counter<k)// no further progress can be made
		{
			global_frequent_counter = vector<int>(k,0);
			frequents = new vector<vector<Frequent*>>(k);
			vector<int>v;
			get_global_frequent(map,0, min_support,v);
			return map;
		}
		global_subset_counter = 0;
		vector<vector<int>> transactions = create_ds( file_name);//read transactions from DB
		for(int trans_ind=0;trans_ind<transactions.size();trans_ind++)//iterating over transactions
		{
			int arr[transactions[trans_ind].size()];
			copy(transactions[trans_ind].begin(),transactions[trans_ind].end(),arr);
			go_down(map,arr,transactions[trans_ind].size(),k, min_support);
		}
	}
}

/*
* This function traverses all nodes of the hash-tree and generates all subsets of the current frequent itemset is
* is run on. Its work is similar to go_down except neither does it create a new node, nor does reach a pruned path
* (if it reaches that, it means an error has occured and something has gone wrong!!!)
*/
void get_associations_rec( unordered_map<int, my_struct*>* map,const int min_support,const float min_confidence,
							  int* arr,int arr_size ,
							  const int count,const vector<int>* whole,
							  vector<int>::iterator seen_begin,vector<int>::iterator seen_end )
{
	for(register int i=0;i<arr_size;i++)
	{
		vector<int> current(seen_begin,seen_end);
		current.push_back(arr[i]);
		register auto t = map->find(arr[i]);

		if(current.size()==whole->size())
			continue;
		if((float)count/t->second->count>=min_confidence) // it is a good rule!
		{
			Association a;
			a.ratio = (float)count/t->second->count;
			a.count = t->second->count;
			a.left = new set<int>(current.begin(),current.end());
			a.right = new vector<int>(whole->begin(), whole->end());
			associations.push_back(a);
		}
		if(arr_size-i>=1)
		{
			get_associations_rec((*map)[arr[i]]->map, min_support, min_confidence, &arr[i+1],arr_size-i-1, 
									count,whole,current.begin(),current.end() );
		}
	}
}

/*
* To find all association rules, iterate oveer them, and for each of them, start from root of the hash-tree,
* and then create all of its subsets in the get_associations_rec function.
*/
void get_associations(unordered_map<int, my_struct*>* map, int min_support, float min_confidence )
{
	for(register int i=2;i<frequents->size();i++)
	{
		for(register int j=0;j<(*frequents)[i].size();j++)
		{
			vector<int>::iterator it;// a useless iterator to pass as the last two args. (it is needed in recursive calls)
			int arr[(*frequents)[i][j]->items.size()];
			copy((*frequents)[i][j]->items.begin(),(*frequents)[i][j]->items.end(),arr);
			get_associations_rec(map, min_support, min_confidence, arr,(*frequents)[i][j]->items.size(), (*frequents)[i][j]->count,&(*frequents)[i][j]->items,it,it );
		}
	}
}

/*
* prints associations as required in the problem description.
* Using printf since it is faster than the overloaded cout!
*/
void print_associations(int total_count)
{
	for(Association a:associations)
	{
		for(register auto j=a.left->begin();j!=a.left->end();j++)
		{
			if(j==a.left->begin())
				printf("%d",*j);
			else
				printf(",%d",*j);
		}
		
		printf(" -> ");
		
		bool first_seen = false;// this is needed to keep track of comma!
		for(register int i=0;i<a.right->size();i++)
		{
			if(first_seen)
			{
				if(a.left->find((*a.right)[i])==a.left->end())
				{
					printf(",%d",(*a.right)[i]);
				}				
			}
			else
			{
				if(a.left->find((*a.right)[i])==a.left->end())
				{
					printf("%d",(*a.right)[i]);
					first_seen = true;
				}				
			}
		}
		printf(" (%.2f,%.2f)\n",(float)a.count/total_count,a.ratio);
	}
}

/*
* print frequent itemsets.
*/
void print_frequent_itemsets(int total_count)
{
	int k;
	for(int i=0;i<frequents->size();i++)
	{
		for(int j=0;j<(*frequents)[i].size();j++)
		{
			for(k=0;k<(*frequents)[i][j]->items.size()-1;k++)
				printf("%d,",(*frequents)[i][j]->items[k]);
			printf("%d",(*frequents)[i][j]->items[k]);
			printf(" (%.2f)\n",(float)(*frequents)[i][j]->count/total_count);
		}
	}
}

/*
* Main Function!
* params: db_file_name, min_support_ratio, min_confidence, x
*		x:	'r' --> print association rules
*			'f' --> print frequent itemsets
*			'a' --> print both
*			'o' --> print their counts
*/
int main(int argc, char* argv[])
{
	const clock_t begin_time = clock();
	// parse the input arguments
	if(argc<4 || argc>5)
	{
		fprintf(stderr,"incorrect number of arguments, terminating the program...\n");
		return 0;
	}
	string db_file_name = string(argv[1]);
	int transaction_count = create_ds(db_file_name).size();
	int min_support = (int) ceil(atof(argv[2])*transaction_count);
	//fprintf(stderr,"min_support: %d\n",min_support);
	float min_confidence = atof(argv[3]);
	char last_arg = (argc==5) ? *(argv[4]) : 'o';

	// now we have the Apriori algorithm and then getting the association rules...
	int max_item = 500;// a good rough number to reserve the map in advance to speed up the process.
	unordered_map<int, my_struct*>* map = run_A_priori(db_file_name, min_support,max_item);
	get_associations(map,min_support,min_confidence);
	
	// printing the required information
	switch (last_arg){
		case 'r':
		{
			print_associations(transaction_count);
			break;
		}
		case 'f':
		{
			print_frequent_itemsets(transaction_count);
			break;
		}
		case 'a':
		{
			print_frequent_itemsets(transaction_count);
			print_associations(transaction_count);
			break;
		}
		case 'o':
		{
			for(int i=0;i<global_frequent_counter.size();i++)
				if(global_frequent_counter[i]>0)
					printf("Number of frequent %d_itemsets: %d\n",i+1,global_frequent_counter[i]);
			printf("Number of association rules: %zu\n",associations.size());
			break;
		}
		default:
		{
			fprintf(stderr,"ERROR! exiting ...\n");
			return 1;
		}
	}
	fprintf(stderr,"%f\n",float( clock () - begin_time ) /  CLOCKS_PER_SEC );
	fflush(stdout);
}

/*
------------------------------------
Note: please comile with this flag: -std=c++0x
------------------------------------
*/