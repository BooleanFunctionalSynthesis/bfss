//Function to reverse substitute skolem functions using wire connections in verilog.
#include <iostream>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <cassert>
#include <string.h>
#include <vector>
#include <algorithm>
#include <boost/tokenizer.hpp>


using namespace std;
//using namespace boost;

#define VERILOG_HEADER "// Generated using revSub.cpp - Does wire based reverse substitution\n"

  typedef boost::tokenizer<boost::char_separator<char> >
    tokenizer;

vector<string> varsY;

//Important assumption : Assuming that the wire connection has to be done by equating nny_i = y_i;
void write_comments (ifstream& ifs, ofstream& ofs, string& line )
{
	while (line.rfind("module", 0))	//Read comments
	{
		ofs << line << endl; 
		getline (ifs, line);	
	}
}
void write_module (ifstream& ifs, ofstream& ofs, string& line )
{
	ofs << line << endl; //TODO: Check that there are no inputs in the line
	getline (ifs, line);	
    string collect ;
    boost::char_separator<char> sep (" ;");

    bool skip = false;

		//Write module
	while (line.find ("output") == string::npos)	 //The next line after the module definition begins from input
	{
        tokenizer tok(line, sep);
		for(tokenizer::iterator beg=tok.begin(); beg!=tok.end();++beg){

            string tok = *beg;
            if (skip && tok.find(",") != string::npos)
                continue;
            else
                if (!skip && tok.find (";") != string::npos)
                {
                    //ofs << ", " ;
                    collect += ", ";
                }
            

            if(tok.find("input") != string::npos)
            {
                ofs << collect << ";" << endl;
                collect= "";
            }


		int pos = tok.find ("nn");
		//cout << "Token" << tok << " Pos " << pos << endl;
	        if (pos < 0) // 0 or 1 
            {
				//ofs << tok << " " ;
		collect += tok + " " ;
                skip = false;
            }
            else
                skip = true;
		}
		getline (ifs, line);	
	}
    if (collect[collect.size() - 2] == ',' )
        collect[collect.size() - 2] = ';';
    else
        collect += ";" ;
    ofs << collect << endl;
	//ofs << ";" << endl;

}
//Save the output variables to a vector
void write_output (ifstream& ifs, ofstream& ofs, string& line)
{
    boost::char_separator<char> sep (", ;");

	//cout << line << endl;
        string collect ;
	while (line.find ("wire") == string::npos && line.find("assign") == string::npos)	//Outputs
	{
        	tokenizer tok(line, sep);
		for(tokenizer::iterator beg=tok.begin(); beg!=tok.end();++beg){

            		string tok = *beg;
			if( tok.find ("output") != string::npos)
				ofs << tok << " " ; 
            else
            {
	 	varsY.push_back(tok);
				   // ofs << tok << ", " ; 
                    collect += tok + " , ";
            }
         }
	 getline (ifs, line);	
	}

    if (collect[collect.size() - 2] == ',' )
        collect[collect.size() - 2] = ';';
    else
        collect += ";" ;
    ofs << collect << endl;
	//ofs << ";" << endl;
	cout << "# Y " << varsY.size() << endl;
    if (varsY.size() == 0)
    {
        cerr << "Error : Could not find any output variables!" << endl;
        ifs.close();
        ofs.close();
        exit (-1);
    }

}

void write_wire (ifstream& ifs, ofstream& ofs, string& line)
{
    boost::char_separator<char> sep (";");
	if (line.find("wire") == string::npos)//no wire def if all sk are constants
		ofs << "wire " << endl;
	while (line.find ("assign") == string::npos)	 //Wire
	{
		if (line.find (";") == string::npos)
		{
			ofs << line << endl;
			getline (ifs, line);	
		}
        else
        {
            tokenizer tok(line, sep);
            for(tokenizer::iterator beg=tok.begin(); beg!=tok.end();++beg){

                string tok = *beg;
                if (tok.find ("wire") != string::npos)
                    ofs << tok << " " ;
                else
                    ofs << tok << ", " ;
            
            }
		    getline (ifs, line);	
         
        }
      }
      for (int i = 0 ; i < varsY.size(); i++) //Add the Y_i's as wires
      {
	   string prefix="";
	   string newName(varsY[i]);
		
	   int pos = newName.find("\\");

	   if (pos == 0) //begins with
	   {
		prefix = "\\";
		newName=varsY[i].substr(pos+1);
		//cout << " prefix " << prefix  << " newName " << newName << endl;
	   }
 
            //cout <<  varsY[i] << " " ;
            if ( i < varsY.size() - 1)
                ofs << prefix << "nn" << newName << " , ";
            else
                ofs << prefix << "nn" << newName << " ; " << endl;
       }
}	
	

void performRevSub ( string norsFname, string rsFname )
{

    char C[100], *tok;
    int tmpVar;

	//FILE *norsFPtr = fopen (norsFileName, "r");
	ifstream ifs (norsFname);

	if (!ifs.is_open ()) {
	cerr <<	"Could not open no rev sub file. Exiting " << endl;
	exit (1);
	}
	ofstream ofs (rsFname, ofstream::out);
	ofs << VERILOG_HEADER;
	// Number of variables and clauses
	string line;
	getline (ifs, line);	

		//Write comments
	write_comments (ifs, ofs, line);
	write_module (ifs, ofs, line);
	write_output( ifs, ofs, line);
    write_wire(ifs, ofs, line);
	//Write output
	//ofs << line <<endl;
	//Write wire
	//getline (ifs, line);	
	while(line.find("endmodule") == string::npos)
	{
		ofs << line << endl;
		getline (ifs, line);	
	}
	for (int i = 0 ; i < varsY.size(); i++) //The 0th element is output
	{

	   string prefix="";
	   string newName(varsY[i]);
		
	   int pos = newName.find("\\");

	   if (pos == 0) //begins with
	   {
		prefix = "\\";
		newName=varsY[i].substr(pos+1);
		//cout << " prefix " << prefix  << " newName " << newName << endl;
	   }
 
            //cout <<  varsY[i] << " " ;
		ofs << "assign " << prefix << "nn" << newName  << " = " << varsY[i] << " ;" << endl;
	}
	ofs << line << endl;

	ifs.close();
	ofs.close();
	exit (1);
}

int main(int argc, char * argv[])
{
	char * qdFileName;
	if ( argc < 2 ) {
		cout << "Wrong number of command-line arguments. Usage: revSub verilog_filename " << endl;
		return 1;
        }
	string norsfname = argv[1];

 	string baseFileName(norsfname);
	baseFileName = baseFileName.substr(baseFileName.find_last_of("/") + 1);  //Get the file name;
	baseFileName.erase(baseFileName.find ("norevsub.v"), string::npos); //This contains the code for the raw file name;
	cout << "BaseName:     " << baseFileName << endl;

	string rsFileName = baseFileName + "result.v";
	performRevSub ( norsfname, rsFileName);
}

