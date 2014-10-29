//********GENERALIZED SUFFIX TREE****************************


//**********This is edited code of Mark Nelson STREE2006.CPP - Suffix tree creation************
//
// STREE2006.CPP - Suffix tree creation
//
// Mark Nelson, updated December, 2006
//
// This code has been tested with Borland C++ and
// Microsoft Visual C++.
//
// This program asks you for a line of input, then
// creates the suffix tree corresponding to the given
// text. Additional code is provided to validate the
// resulting tree after creation.
//
#include <iostream>
#include <iomanip>
#include <cstdlib>
#include <string.h>
#include <cassert>
#include <string>
#include <list>
#include <algorithm>

using std::cout;
using std::cin;
using std::cerr;
using std::setw;
using std::flush;
using std::endl;


//
// When a new tree is added to the table, we step
// through all the currently defined suffixes from
// the active point to the end point.  This structure
// defines a Suffix by its final character.
// In the canonical representation, we define that last
// character by starting at a node in the tree, and
// following a string of characters, represented by
// first_char_index and last_char_index.  The two indices
// point into the input string.  Note that if a suffix
// ends at a node, there are no additional characters
// needed to characterize its last character position.
// When this is the case, we say the node is Explicit,
// and set first_char_index > last_char_index to flag
// that.
//

class Suffix {
public:
    int origin_node;
    int first_char_index;
    int last_char_index;

    Suffix(int node, int start, int stop)
    : origin_node(node),
    first_char_index(start),
    last_char_index(stop) {
    };

    int Explicit() {
        return first_char_index > last_char_index;
    }

    int Implicit() {
        return last_char_index >= first_char_index;
    }
    void Canonize();
};

//
// The suffix tree is made up of edges connecting nodes.
// Each edge represents a string of characters starting
// at first_char_index and ending at last_char_index.
// Edges can be inserted and removed from a hash table,
// based on the Hash() function defined here.  The hash
// table indicates an unused slot by setting the
// start_node value to -1.
//

class Edge {
public:
    int first_char_index;
    int last_char_index;
    int end_node;
    int start_node;
    int depth_of_end_node; //keep character depth from the root
    void Insert();
    void Remove();
    Edge();
    Edge(int init_first_char_index,
            int init_last_char_index,
            int parent_node);
    int SplitEdge(Suffix &s);
    static Edge Find(int node, int c);
    static int Hash(int node, int c);
};

//
//  The only information contained in a node is the
//  suffix link. Each suffix in the tree that ends
//  at a particular node can find the next smaller suffix
//  by following the suffix_node link to a new node.  Nodes
//  are stored in a simple array.
//

//Modified by daham
//I have added fields length_from_root,isLeaf,parentNode,termination_label

class Node {
public:
    int suffix_node;
    int length_from_root; //keep character depth from the root
    char termination_label;
    int isLeaf;
    int parentNode;

    Node() {
        suffix_node = -1;
    }
    static int Count;
};

//
// The maximum input string length this program
// will handle is defined here.  A suffix tree
// can have as many as 2N edges/nodes.  The edges
// are stored in a hash table, whose size is also
// defined here.
//
const int MAX_LENGTH = 1000;
const int HASH_TABLE_SIZE = 2179; //A prime roughly 10% larger

//
// This is the hash table where all the currently
// defined edges are stored.  You can dump out
// all the currently defined edges by iterating
// through the table and finding edges whose start_node
// is not -1.
//

Edge Edges[ HASH_TABLE_SIZE ];

//
// The array of defined nodes.  The count is 1 at the
// start because the initial tree has the root node
// defined, with no children.
//

int Node::Count = 1;
Node Nodes[ MAX_LENGTH * 2 ];
int size;
int string_size;
int required[100];

//
// The input buffer and character count.  Please note that N
// is the length of the input string -1, which means it
// denotes the maximum index in the input buffer.
//

char T[ MAX_LENGTH ];
char string_input[ MAX_LENGTH];
char string_in[ MAX_LENGTH];
int current_end;
int start = 0;
int entity_count = 0;
int N;

//
// Necessary forward references
//
void validate();
int walk_tree(int start_node, int last_char_so_far);
void store(Suffix active, char string_input[ MAX_LENGTH ]);
void search(char doc_id);
void store_eligible_entities();


//
// The default ctor for Edge just sets start_node
// to the invalid value.  This is done to guarantee
// that the hash table is initially filled with unused
// edges.
//

Edge::Edge() {
    start_node = -1;
}

//
// I create new edges in the program while walking up
// the set of suffixes from the active point to the
// endpoint.  Each time I create a new edge, I also
// add a new node for its end point.  The node entry
// is already present in the Nodes[] array, and its
// suffix node is set to -1 by the default Node() ctor,
// so I don't have to do anything with it at this point.
//

Edge::Edge(int init_first, int init_last, int parent_node) {
    first_char_index = init_first;
    last_char_index = init_last;
    start_node = parent_node;
    end_node = Node::Count++;
    Nodes[end_node].parentNode = parent_node;

    Nodes[end_node].termination_label = T[last_char_index];
    depth_of_end_node = 0;

}

//
// Edges are inserted into the hash table using this hashing
// function.
//

int Edge::Hash(int node, int c) {
    return ( (node << 8) + c) % HASH_TABLE_SIZE;
}

//
// A given edge gets a copy of itself inserted into the table
// with this function.  It uses a linear probe technique, which
// means in the case of a collision, we just step forward through
// the table until we find the first unused slot.
//

void Edge::Insert() {
    int i = Hash(start_node, T[ first_char_index ]);
    while (Edges[ i ].start_node != -1)
        i = ++i % HASH_TABLE_SIZE;
    Edges[ i ] = *this;
}

//
// Removing an edge from the hash table is a little more tricky.
// You have to worry about creating a gap in the table that will
// make it impossible to find other entries that have been inserted
// using a probe.  Working around this means that after setting
// an edge to be unused, we have to walk ahead in the table,
// filling in gaps until all the elements can be found.
//
// Knuth, Sorting and Searching, Algorithm R, p. 527
//

void Edge::Remove() {
    int i = Hash(start_node, T[ first_char_index ]);
    while (Edges[ i ].start_node != start_node ||
            Edges[ i ].first_char_index != first_char_index)
        i = ++i % HASH_TABLE_SIZE;
    for (;;) {
        Edges[ i ].start_node = -1;
        int j = i;
        for (;;) {
            i = ++i % HASH_TABLE_SIZE;
            if (Edges[ i ].start_node == -1)
                return;
            int r = Hash(Edges[ i ].start_node, T[ Edges[ i ].first_char_index ]);
            if (i >= r && r > j)
                continue;
            if (r > j && j > i)
                continue;
            if (j > i && i >= r)
                continue;
            break;
        }
        Edges[ j ] = Edges[ i ];
    }
}

//
// The whole reason for storing edges in a hash table is that it
// makes this function fairly efficient.  When I want to find a
// particular edge leading out of a particular node, I call this
// function.  It locates the edge in the hash table, and returns
// a copy of it.  If the edge isn't found, the edge that is returned
// to the caller will have start_node set to -1, which is the value
// used in the hash table to flag an unused entry.
//

Edge Edge::Find(int node, int c) {
    int i = Hash(node, c);
    for (;;) {
        if (Edges[ i ].start_node == node)
            if (c == T[ Edges[ i ].first_char_index ])
                return Edges[ i ];
        if (Edges[ i ].start_node == -1)
            return Edges[ i ];
        i = ++i % HASH_TABLE_SIZE;
    }
}

//
// When a suffix ends on an implicit node, adding a new character
// means I have to split an existing edge.  This function is called
// to split an edge at the point defined by the Suffix argument.
// The existing edge loses its parent, as well as some of its leading
// characters.  The newly created edge descends from the original
// parent, and now has the existing edge as a child.
//
// Since the existing edge is getting a new parent and starting
// character, its hash table entry will no longer be valid.  That's
// why it gets removed at the start of the function.  After the parent
// and start char have been recalculated, it is re-inserted.
//
// The number of characters stolen from the original node and given
// to the new node is equal to the number of characters in the suffix
// argument, which is last - first + 1;
//

int Edge::SplitEdge(Suffix &s) {
    Remove();
    Edge *new_edge =
            new Edge(first_char_index,
            first_char_index + s.last_char_index - s.first_char_index,
            s.origin_node);
    // new_edge->depth_of_end_node=s.last_char_index - s.first_char_index;//initialize end node depth
    new_edge->Insert();
    Nodes[ new_edge->end_node ].suffix_node = s.origin_node;

    Nodes[ new_edge->end_node ].length_from_root = Nodes[new_edge->start_node].length_from_root + new_edge->last_char_index - new_edge->first_char_index + 1;
    Nodes[new_edge->end_node].termination_label = T[new_edge->last_char_index];
    Nodes[s.origin_node].isLeaf = 0;
    first_char_index += s.last_char_index - s.first_char_index + 1;
    start_node = new_edge->end_node;
    //depth_of_end_node-=s.last_char_index - s.first_char_index;
    Insert();
    Nodes[ end_node ].length_from_root = Nodes[ start_node ].length_from_root + last_char_index - first_char_index + 1;
    Nodes[end_node].termination_label = T[last_char_index];
    return new_edge->end_node;
}

//Modified by daham
//This type objects are ultimately stored in the memory as the
//resltant tree

class TreeEntity {
public:
    int end_node;
    std::string sequence;
    char termination_char;
    int parent;
    int depth;

    bool operator<(const TreeEntity& rhs) {
        return depth < rhs.depth;
    }

};
std::list<char> terminators;
//Modified by daham
//Array of Tree Entities
TreeEntity TreeEntities[MAX_LENGTH * 2];
//This type of array is ultimately kept
TreeEntity EligibleEntities[MAX_LENGTH * 2];


//Modified by daham
//Tree Entities are updated by newly added field values

void dump_edges(int current_n) {

    cout << " Start  End  Suf  First Last  String   depth isLeaf terminationLabel\n";

    for (int j = 0; j < HASH_TABLE_SIZE; j++) {

        Edge *s = Edges + j;

        if (s->start_node == -1)
            continue;
        cout << setw(5) << s->start_node << " "
                << setw(5) << s->end_node << " "
                << setw(3) << Nodes[ s->end_node ].suffix_node << " "
                << setw(5) << s->first_char_index << " "
                //<< setw(6) << Nodes[s->end_node].length_from_root  << "  ";
                << setw(6) << s->last_char_index << "  ";
        TreeEntities[s->end_node ].end_node = s->end_node;
        int top;
        if (current_n > s->last_char_index)
            top = s->last_char_index;
        else
            top = current_n;
        //        cout<<"Node entitiy is "
        //                << s->end_node;
        for (int l = s->first_char_index;
                l <= top;
                l++) {

            TreeEntities[s->end_node ].sequence = TreeEntities[s->end_node ].sequence + T[l]; //******************************
            //           cout<< " charatcter is :"
            //                    <<T[l]
            //                    <<" sequence is :"
            //                    <<TreeEntities[s->end_node ].sequence;
            // cout << T[ l ];
        }
        // int x;
        // for (x = 0; x<sizeof (TreeEntities[y].sequence); x++)
        cout << TreeEntities[s->end_node ].sequence;
        cout << "";

        cout << setw(6) << Nodes[s->end_node].length_from_root << " -->";
        TreeEntities[s->end_node ].depth = Nodes[s->end_node].length_from_root;
        // cout << setw(6) << TreeEntities[y].depth << " -->";
        cout << setw(10) << Nodes[s->end_node].isLeaf << "--> ";
        cout << setw(10) << Nodes[s->end_node].termination_label << "  ";
        TreeEntities[s->end_node ].termination_char = Nodes[s->end_node].termination_label;
        cout << "\n";
        cout << TreeEntities[s->end_node ].end_node
                << ","
                << TreeEntities[s->end_node ].depth
                << "\n";
        TreeEntities[s->end_node ].parent = s->start_node;
        cout << "length of the string ___________________________"
                << TreeEntities[s->end_node ].sequence.length();
        // cout<<"++++++++++++++"
        // <<sizeof(int)*3+sizeof(char)+TreeEntities[s->end_node ].sequence.length()*sizeof(char);
        // size=size+sizeof(int)*3+sizeof(char)+TreeEntities[s->end_node ].sequence.length()*sizeof(char);
        size += TreeEntities[s->end_node ].sequence.length();
        cout
                << ">>>>"
                << size
                << "]]]]";
    }

    cout << "size of the tree: "
            << size
            << "\n";


}

//
// A suffix in the tree is denoted by a Suffix structure
// that denotes its last character.  The canonical
// representation of a suffix for this algorithm requires
// that the origin_node by the closest node to the end
// of the tree.  To force this to be true, we have to
// slide down every edge in our current path until we
// reach the final node.

void Suffix::Canonize() {
    if (!Explicit()) {
        Edge edge = Edge::Find(origin_node, T[ first_char_index ]);
        int edge_span = edge.last_char_index - edge.first_char_index;
        while (edge_span <= (last_char_index - first_char_index)) {
            first_char_index = first_char_index + edge_span + 1;
            origin_node = edge.end_node;
            if (first_char_index <= last_char_index) {
                edge = Edge::Find(edge.end_node, T[ first_char_index ]);
                edge_span = edge.last_char_index - edge.first_char_index;
            };
        }
    }
}

//
// This routine constitutes the heart of the algorithm.
// It is called repetitively, once for each of the prefixes
// of the input string.  The prefix in question is denoted
// by the index of its last character.
//
// At each prefix, we start at the active point, and add
// a new edge denoting the new last character, until we
// reach a point where the new edge is not needed due to
// the presence of an existing edge starting with the new
// last character.  This point is the end point.
//
// Luckily for use, the end point just happens to be the
// active point for the next pass through the tree.  All
// we have to do is update it's last_char_index to indicate
// that it has grown by a single character, and then this
// routine can do all its work one more time.
//

void AddPrefix(Suffix &active, int last_char_index) {
    int parent_node;
    int last_parent_node = -1;

    cout << "considering"
            << active.origin_node;
    cout << "last char index "
            << last_char_index
            << "\n";

    for (;;) {
        Edge edge;
        parent_node = active.origin_node;
        //
        // Step 1 is to try and find a matching edge for the given node.
        // If a matching edge exists, we are done adding edges, so we break
        // out of this big loop.
        //

        if (active.Explicit()) {
            edge = Edge::Find(active.origin_node, T[ last_char_index ]);

            if (edge.start_node != -1) {
                Nodes[edge.end_node].length_from_root = Nodes[edge.start_node].length_from_root + edge.last_char_index - edge.first_char_index + 1;
                Nodes[edge.end_node].termination_label = T[edge.last_char_index];
                break;
            }


        } else { //implicit node, a little more complicated
            edge = Edge::Find(active.origin_node, T[ active.first_char_index ]);
            int span = active.last_char_index - active.first_char_index;
            if (T[ edge.first_char_index + span + 1 ] == T[ last_char_index ])
                break;
            parent_node = edge.SplitEdge(active);
        }
        //
        // We didn't find a matching edge, so we create a new one, add
        // it to the tree at the parent node position, and insert it
        // into the hash table.  When we create a new node, it also
        // means we need to create a suffix link to the new node from
        // the last node we visited.
        //
        Edge *new_edge = new Edge(last_char_index, N, parent_node);
        //new_edge->depth_of_end_node=1;//initialize end node depth
        Nodes[new_edge->end_node].isLeaf = 1;
        Nodes[new_edge->end_node].termination_label = T[new_edge->last_char_index];
        new_edge->Insert();


        Nodes[new_edge->end_node].length_from_root = Nodes[new_edge->start_node].length_from_root + new_edge->last_char_index - new_edge->first_char_index + 1;
        if (last_parent_node > 0)
            Nodes[ last_parent_node ].suffix_node = parent_node;
        last_parent_node = parent_node;
        //
        // This final step is where we move to the next smaller suffix
        //
        if (active.origin_node == 0)
            active.first_char_index++;
        else
            active.origin_node = Nodes[ active.origin_node ].suffix_node;
        active.Canonize();
    }
    if (last_parent_node > 0)
        Nodes[ last_parent_node ].suffix_node = parent_node;
    active.last_char_index++; //Now the endpoint is the next active point
    active.Canonize();
};

int main() {

    cout << "Normally, suffix trees require that the last\n"
            << "character in the input string be unique.  If\n"
            << "you don't do this, your tree will contain\n"
            << "suffixes that don't end in leaf nodes.  This is\n"
            << "often a useful requirement. You can build a tree\n"
            << "in this program without meeting this requirement,\n"
            << "but the validation code will flag it as being an\n"
            << "invalid tree\n\n";
    cout << "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<";
    Suffix active(0, 0, -1); // The initial active prefix




    for (int x = 0; x < 5; x++) {
        cout << "Enter string: " << flush;
        for (std::string line; std::getline(std::cin, line);) {
            
            if (line.length() == 0) {
                break;
            }
            for (int z = 0; z < line.length(); z++) {
                string_in[z] = line[z];
            }

            // strcat(T, line);
        }
       
        string_in[strlen(string_in)] = (char) (x + 33);
        terminators.push_back((char) (x + 33));

        cout << "last character for "
                << x
                << " is "
                << string_in[11]
                << " ";

        for (int g = 0; g <= 11; g++) {

            cout << string_in[g];
        }
        cout << "\n";
        store(active, string_in);
    }
    //    store(active, "aaaaaae$");
    //    terminators.push_back('$');
    //    store(active, "aaaaaax#");
    //    terminators.push_back('#');
    //    store(active, "aaaaaai)");
    //    terminators.push_back(')');
    //    store(active, "aaaaaap*");
    //    terminators.push_back('*');
    //    store(active, "aaaaaak-");
    //    terminators.push_back('-');
    //    store(active, "aaaaaam=");
    //    terminators.push_back('=');

    //:::::::::::::::::::::::::::::::::::::::
    //     store(active, "aaavaaaa^");
    //    terminators.push_back('^');
    //    store(active, "aaaanaaa*");
    //    terminators.push_back('#');
    //     store(active, "haaaaa(");
    //    terminators.push_back('(');
    //    store(active, "gaaaaab-");
    //    terminators.push_back('-');
    // store(active,"y");
    dump_edges(N);
    store_eligible_entities();
    search('$');
    //search('$');
    //    while (true) {
    //        cout << "Enter string: " << flush;
    //
    //        cin.getline(string_input, 99);
    //        strcat(T, string_input);
    //        N = strlen(T) - 1;
    //
    //
    //
    //        //
    //        // The active point is the first non-leaf suffix in the
    //        // tree.  We start by setting this to be the empty string
    //        // at node 0.  The AddPrefix() function will update this
    //        // value after every new prefix is added.
    //        //
    //
    //        for (int i = start; i <= N; i++)
    //            AddPrefix(active, i);
    //        //
    //        // Once all N prefixes have been added, the resulting table
    //        // of edges is printed out, and a validation step is
    //        // optionally performed.
    //        //
    //        dump_edges(N);
    //        start = N + 1;
    //    }
    cout << "Would you like to validate the tree?"
            << flush;
    std::string s;
    getline(cin, s);
    if (s.size() > 0 && s[ 0 ] == 'Y' || s[ 0 ] == 'y')
        validate();
    return 1;
};

void store(Suffix active, char string_input[ MAX_LENGTH]) {
    cout << "Here is the string you enterer   ";
    for (int f = 0; f < strlen(string_input); f++) {
        cout << string_input[f]
                << " ";
    }


    std::string str;
    //    cout << "Enter string: " << flush;
    //    for (std::string line; std::getline(std::cin, line);) {
    //        //std::cout << line << std::endl;
    //        if(line.length()==0){break;}
    //        for(int z=0;z<line.length();z++){
    //            string_input[z]=line[z];
    //        }
    //        
    //       // strcat(T, line);
    //    }
    //*********************************************************
    // while(cin){

    // cin.getline(string_input, 99);

    //}
    strcat(T, string_input);
    N = strlen(T) - 1;
    cout << "size of string: "
            << strlen(T)//*sizeof(char)
            << "\n";


    //
    // The active point is the first non-leaf suffix in the
    // tree.  We start by setting this to be the empty string
    // at node 0.  The AddPrefix() function will update this
    // value after every new prefix is added.
    //

    for (int i = start; i <= N; i++)
        AddPrefix(active, i);
    //
    // Once all N prefixes have been added, the resulting table
    // of edges is printed out, and a validation step is
    // optionally performed.
    //

    start = N + 1;
}
std::list<TreeEntity> entity_list;

void search(char doc_id) {
    TreeEntity next;

    cout << doc_id
            << "\n";


    int i;
    int j = 0;
    int k;



    for (int m = 0; m < 100
            ; m++) {
        if (Nodes[TreeEntities[m].end_node].isLeaf == 1 && Nodes[TreeEntities[m].end_node].termination_label == doc_id) {

            entity_list.push_back(TreeEntities[m]);
            cout << ",,,,,,,,,,,,,,,,,,"
                    << TreeEntities[m].termination_char;

        }


    }

    // entity_list.sort();
    entity_list.sort();
    TreeEntity entity = entity_list.back();
    char resultString[MAX_LENGTH];
    cout << "Here is the VALUE :::::"
            << entity.depth
            << " "
            << entity.end_node
            << "\n";

    /// Nodes[entity.end_node].parentNode
    cout << "Here are the strings :";
    k = entity.end_node;
    next = TreeEntities[k];

    cout << k
            << next.sequence;
    while (k != 0) {

        k = TreeEntities[k].parent;
        next = TreeEntities[k];

        cout << k
                << next.sequence;
    }
    cout << "\n\n";

}

void store_eligible_entities() {

    TreeEntity next;




    int i;
    int j = 0;
    int k;


    for (std::list<char>::iterator it = terminators.begin(); it != terminators.end(); it++) {
        entity_list.clear();
        cout << *it
                <<"IIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIINNNNNN"
                << *it
                << *it
                << "\n";
        for (int m = 0; m < 1000
                ; m++) {
            if (Nodes[TreeEntities[m].end_node].isLeaf == 1 && Nodes[TreeEntities[m].end_node].termination_label == *it) {

                entity_list.push_back(TreeEntities[m]);
                cout << ",,,,,,,,,,,,,,,,,,"
                        << TreeEntities[m].termination_char;

            }


        }

        // entity_list.sort();
        entity_list.sort();
        TreeEntity entity = entity_list.back();
        char resultString[MAX_LENGTH];
        cout << "Here is the VALUE :::::"
                << entity.depth
                << " "
                << entity.end_node
                << "\n";

        /// Nodes[entity.end_node].parentNode
        cout << "Here are the strings :";
        k = entity.end_node;
        next = TreeEntities[k];
        EligibleEntities[k] = TreeEntities[k];
        cout << k
                << next.sequence;
        while (k != 0) {

            k = TreeEntities[k].parent;
            next = TreeEntities[k];
            EligibleEntities[k] = TreeEntities[k];
            cout << k
                    << next.sequence;
        }
        cout << "\n\n";

    }
    int length_final;
    for (int b = 0; b < 100; b++) {
        length_final += EligibleEntities[b].sequence.length();
    }
    cout << "MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM:"
            << length_final
            << "\n";
}

//
// The validation code consists of two routines.  All it does
// is traverse the entire tree.  walk_tree() calls itself
// recursively, building suffix strings up as it goes.  When
// walk_tree() reaches a leaf node, it checks to see if the
// suffix derived from the tree matches the suffix starting
// at the same point in the input text.  If so, it tags that
// suffix as correct in the GoodSuffixes[] array.  When the tree
// has been traversed, every entry in the GoodSuffixes array should
// have a value of 1.
//
// In addition, the BranchCount[] array is updated while the tree is
// walked as well.  Every count in the array has the
// number of child edges emanating from that node.  If the node
// is a leaf node, the value is set to -1.  When the routine
// finishes, every node should be a branch or a leaf.  The number
// of leaf nodes should match the number of suffixes (the length)
// of the input string.  The total number of branches from all
// nodes should match the node count.
//

char CurrentString[ MAX_LENGTH ];
char GoodSuffixes[ MAX_LENGTH ];
char BranchCount[ MAX_LENGTH * 2 ] = {0};

void validate() {
    for (int i = 0; i < N; i++)
        GoodSuffixes[ i ] = 0;
    walk_tree(0, 0);
    int error = 0;
    for (int i = 0; i < N; i++)
        if (GoodSuffixes[ i ] != 1) {
            cout << "Suffix " << i << " count wrong!\n";
            error++;
        }
    if (error == 0)
        cout << "All Suffixes present!\n";
    int leaf_count = 0;
    int branch_count = 0;
    for (int i = 0; i < Node::Count; i++) {
        if (BranchCount[ i ] == 0)
            cout << "Logic error on node "
                << i
                << ", not a leaf or internal node!\n";
        else if (BranchCount[ i ] == -1)
            leaf_count++;
        else
            branch_count += BranchCount[ i ];
    }
    cout << "Leaf count : "
            << leaf_count
            << (leaf_count == (N + 1) ? " OK" : " Error!")
            << "\n";
    cout << "Branch count : "
            << branch_count
            << (branch_count == (Node::Count - 1) ? " OK" : " Error!")
            << endl;
}

int walk_tree(int start_node, int last_char_so_far) {
    int edges = 0;
    for (int i = 0; i < 256; i++) {
        Edge edge = Edge::Find(start_node, i);
        if (edge.start_node != -1) {
            if (BranchCount[ edge.start_node ] < 0)
                cerr << "Logic error on node "
                    << edge.start_node
                    << '\n';
            BranchCount[ edge.start_node ]++;
            edges++;
            int l = last_char_so_far;
            for (int j = edge.first_char_index; j <= edge.last_char_index; j++)
                CurrentString[ l++ ] = T[ j ];
            CurrentString[ l ] = '\0';
            if (walk_tree(edge.end_node, l)) {
                if (BranchCount[ edge.end_node ] > 0)
                    cerr << "Logic error on node "
                        << edge.end_node
                        << "\n";
                BranchCount[ edge.end_node ]--;
            }
        }
    }
    //
    // If this node didn't have any child edges, it means we
    // are at a leaf node, and can check on this suffix.  We
    // check to see if it matches the input string, then tick
    // off it's entry in the GoodSuffixes list.
    //
    if (edges == 0) {
        cout << "Suffix : ";
        for (int m = 0; m < last_char_so_far; m++)
            cout << CurrentString[ m ];
        cout << "\n";
        GoodSuffixes[ strlen(CurrentString) - 1 ]++;
        cout << "comparing: " << (T + N - strlen(CurrentString) + 1)
                << " to " << CurrentString << endl;
        if (strcmp(T + N - strlen(CurrentString) + 1, CurrentString) != 0)
            cout << "Comparison failure!\n";
        return 1;
    } else
        return 0;
}

