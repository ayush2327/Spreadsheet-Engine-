#include <bits/stdc++.h>
using namespace std;
#define int long long
const int inf = LLONG_MAX;
const int EVAL_ERROR = LLONG_MIN;

class segtree{
	private:
	
	struct Node{
		vector<int> seg;
		Node(int node , int null) : seg(2*node , null) {}
	};
	
	int n , m , null , node_out , node_in;
	string operation;
	vector<Node> seg;
	
	void build(){
		node_out = node_in = 1;
		
		while(node_out < n){
			node_out *= 2;
		}
		
		while(node_in < m){
			node_in *= 2;
		}
		
		seg.resize(2*node_out , Node(node_in , null));
	}
	
	void merge(int i , int j){
		if(i < node_out){
			if(operation == "SUM") seg[i].seg[j] = seg[2*i].seg[j] + seg[2*i + 1].seg[j];
			else if(operation == "MAX") seg[i].seg[j] = max(seg[2*i].seg[j] , seg[2*i + 1].seg[j]);
			else if(operation == "MIN") seg[i].seg[j] = min(seg[2*i].seg[j] , seg[2*i + 1].seg[j]);
		}
		else if(j < node_in){
			if(operation == "SUM") seg[i].seg[j] = seg[i].seg[2*j] + seg[i].seg[2*j + 1];
			else if(operation == "MAX") seg[i].seg[j] = max(seg[i].seg[2*j] , seg[i].seg[2*j + 1]);
			else if(operation == "MIN") seg[i].seg[j] = min(seg[i].seg[2*j] , seg[i].seg[2*j + 1]);
		}
	}
	
	void update_row(int row , int i , int x){
		seg[row].seg[i] = x , i /= 2;
		while(i >= 1){
			merge(row , i);
			i>>=1;
		}
	}
	
	int get_row(auto &row , int l , int r){
		int res = null;
		while(l <= r){
			if(l&1){
				if(operation == "SUM") res += row[l++];
				else if(operation == "MAX") res = max(res , row[l++]);
				else if(operation == "MIN") res = min(res , row[l++]);
			}
			if(r%2 == 0){
				if(operation == "SUM") res += row[r--];
				else if(operation == "MAX") res = max(res , row[r--]);
				else if(operation == "MIN") res = min(res , row[r--]);
			}
			l>>=1 , r>>=1;
		}
		return res;
	}
		
	public:
	segtree() { n = m = null = 0 , operation = "NONE"; }
	segtree(int n1 , int m1 , int null1 , string op) : n(n1) , m(m1) ,
	null(null1) , operation(op) { build(); }
	
	void update(int i , int j , int x){
		i += node_out , j += node_in;
		update_row(i , j , x) , i /= 2;
		
		while(i >= 1){
			int col = j;
			while(col >= 1){
				merge(i , col);
				col>>=1;
			}
			i>>=1;
		}
	}
	
	int get(int lx , int ly , int rx , int ry){
		int res = null;
		lx += node_out , rx += node_out;
		ly += node_in , ry += node_in;
		
		while(lx <= rx){
			if(lx&1){
				if(operation == "SUM") res += get_row(seg[lx++].seg , ly , ry);
				else if(operation == "MAX") res = max(res , get_row(seg[lx++].seg , ly , ry));
				else if(operation == "MIN") res = min(res , get_row(seg[lx++].seg , ly , ry));
			}
			if(rx%2 == 0){
				if(operation == "SUM") res += get_row(seg[rx--].seg , ly , ry);
				else if(operation == "MAX") res = max(res , get_row(seg[rx--].seg , ly , ry));
				else if(operation == "MIN") res = min(res , get_row(seg[rx--].seg , ly , ry));
			}
			lx>>=1 , rx>>=1;
		}
		
		return res;
	}
	
};

string trim(const string& str) {
    size_t first = str.find_first_not_of(' ');
    if (first == string::npos) return "";
    size_t last = str.find_last_not_of(' ');
    return str.substr(first, last - first + 1);
}

class make_sheet {
private:

	int R, C;
   int start_row = 1, start_col = 1;
	vector<vector<int>> sheet;
   vector<string> col;
	map<int , bool> vis;
	map<int , set<pair<int , string>>> graph , rev_graph;
	segtree seg_sum , seg_min;
	segtree seg_max , seg_square_sum;
	
	void init(){
		seg_sum = segtree(R + 1, C + 1, 0, "SUM");
		seg_min = segtree(R + 1, C + 1, LLONG_MAX, "MIN");
		seg_max = segtree(R + 1, C + 1, LLONG_MIN, "MAX");
		seg_square_sum = segtree(R + 1, C + 1, 0, "SUM");
	}
	
private:
	 
    int find_col(string_view s) {
        auto it = find(col.begin(), col.end(), s);
        if (it == col.end()) return -1;
        return it - col.begin();
    }

    pair<int, int> parse_cell_reference(string_view ref) {
        static const regex cell_regex(R"(([A-Z]+)([0-9]+))");
        smatch match;
        string ref_str(ref);
        if (!regex_match(ref_str, match, cell_regex)) return {-1, -1};

        string col_str = match[1];
        int row = stoll(match[2]);
        int col_id = find_col(col_str);
        if (col_id == -1) return {-1, -1};
        return {row, col_id};
    }

    vector<array<int, 2>> parse_range(string_view range_str) {
        size_t colon_pos = range_str.find(':');
        if (colon_pos == string_view::npos) {
            auto [r, c] = parse_cell_reference(range_str);
            if (r == -1 || c == -1) return {};
            return { {r, c}, {r, c} };
        }

        auto start_str = range_str.substr(0, colon_pos);
        auto end_str = range_str.substr(colon_pos + 1);

        auto [r1, c1] = parse_cell_reference(start_str);
        auto [r2, c2] = parse_cell_reference(end_str);

        if (r1 == -1 || c1 == -1 || r2 == -1 || c2 == -1) return {};
        if (r1 > r2 || c1 > c2) return {};

        return { {r1, c1}, {r2, c2} };
    }

   int evaluate_cell(int r, int c){
        if (r < 1 || r > R || c < 1 || c > C) return EVAL_ERROR;
        return sheet[r][c];
    }

   int evaluate_operand(string_view token) {
        auto [r, c] = parse_cell_reference(token);
        if (r != -1 && c != -1) return evaluate_cell(r, c);

        for (char ch : token) if (!isdigit(ch) && ch != '-') return EVAL_ERROR;
        return stoll(string(token));
    }
	
	int evaluate_function(string_view func_name, string_view range_str){
		 auto range = parse_range(range_str);
		 if (range.empty()) return EVAL_ERROR;

		 int r1 = range[0][0], c1 = range[0][1];
		 int r2 = range[1][0], c2 = range[1][1];
		 
		 if(func_name == "SUM"){
			 return seg_sum.get(r1 , c1 , r2 , c2);
		 }
		 if(func_name == "MIN"){
			 return seg_min.get(r1 , c1 , r2 , c2);
		 }
		 if(func_name == "MAX"){
			 return seg_max.get(r1 , c1 , r2 , c2);
		 }
		 if(func_name == "AVG"){
			 double val = seg_sum.get(r1 , c1 , r2 , c2);
			 val = val /((r2 - r1 + 1) * (c2 - c1 + 1));
			 return (int)val;
		 }
		 if(func_name == "STDEV"){
			 double avg = seg_sum.get(r1 , c1 , r2 , c2);
			 avg = avg / ((r2 - r1 + 1) * (c2 - c1 + 1));
			 double square_sum = seg_square_sum.get(r1 , c1 , r2 , c2);
			 square_sum = square_sum / ((r2 - r1 + 1) * (c2 - c1  + 1));
			 
			 double variance = square_sum - avg * avg;
			 return (int)sqrtl(variance);
		 }
		 
		 return EVAL_ERROR;
	}

	int evaluate_expression(string_view expr) {
		 string s = trim(string(expr));

		 // Handle functions like SUM(A1:B2), MIN(...), MAX(...)
		 if (s.starts_with("SUM(") && s.back() == ')'){
			  return evaluate_function("SUM", s.substr(4, s.size() - 5));
		 }
		 else if (s.starts_with("MIN(") && s.back() == ')'){
			  return evaluate_function("MIN", s.substr(4, s.size() - 5));
		 }
		 else if (s.starts_with("MAX(") && s.back() == ')'){
			  return evaluate_function("MAX", s.substr(4, s.size() - 5));
		 }
		 else if(s.starts_with("AVG(") && s.back() == ')'){
			 return evaluate_function("AVG", s.substr(4, s.size() - 5));
		 }
		 else if(s.starts_with("STDEV(") && s.back() == ')'){
			 return evaluate_function("STDEV", s.substr(6, s.size() - 7));
		 }

		 // Handle binary operators
		 size_t pos = string::npos;
		 char op = 0;

		 for (char candidate : {'+', '-', '*', '/'}) {
			  pos = s.find(candidate);
			  if (pos != string::npos) {
					op = candidate;
					break;
			  }
		 }

		 if (pos == string::npos) return evaluate_operand(s);

		 string_view left = s.substr(0, pos);
		 string_view right = s.substr(pos + 1);

		 int left_val = evaluate_operand(trim(string(left)));
		 int right_val = evaluate_operand(trim(string(right)));

		 if (left_val == EVAL_ERROR || right_val == EVAL_ERROR) return EVAL_ERROR;

		 if (op == '/' && right_val == 0) {
			  cout << "Error: Division by zero. Please enter a valid expression.\n";
			  return EVAL_ERROR;
		 }

		 switch (op) {
			  case '+': return left_val + right_val;
			  case '-': return left_val - right_val;
			  case '*': return left_val * right_val;
			  case '/': return left_val / right_val;
		 }

		 return EVAL_ERROR;
	}
	
	void cycle_check(int u){
		vis[u] = 1;
		for(auto &[i , value] : graph[u]) cycle_check(i);
	}
	
	void update_dependency(int u){
		for(auto &[i , formula] : graph[u]){
			
			int row_id , col_id;
			if(i % C == 0) row_id = i/C , col_id = C;
			else row_id = i/C + 1 , col_id = i % C;
			
			sheet[row_id][col_id] = evaluate_expression(formula);
			seg_square_sum.update(row_id , col_id , sheet[row_id][col_id] * sheet[row_id][col_id]);
			seg_sum.update(row_id , col_id , sheet[row_id][col_id]);
			seg_min.update(row_id , col_id , sheet[row_id][col_id]);
			seg_max.update(row_id , col_id , sheet[row_id][col_id]);
			
			update_dependency(i);
		}
	}

public:
    make_sheet(int r, int c) : R(r), C(c), sheet(r + 1, vector<int>(c + 1)), col(c + 1) {
        col[0] = " ";
        int l = 1;

        for (char c1 = 'A'; c1 <= 'Z' && l <= C; ++c1)
            col[l++] = string(1, c1);

        for (char c1 = 'A'; c1 <= 'Z' && l <= C; ++c1){
            for (char c2 = 'A'; c2 <= 'Z' && l <= C; ++c2) {
                string temp;
                temp.push_back(c1);
                temp.push_back(c2);
                col[l++] = temp;
            }
		  }

        for (char c1 = 'A'; c1 <= 'Z' && l <= C; ++c1){
            for (char c2 = 'A'; c2 <= 'Z' && l <= C; ++c2){
                for (char c3 = 'A'; c3 <= 'Z' && l <= C; ++c3) {
                    string temp;
                    temp.push_back(c1);
                    temp.push_back(c2);
                    temp.push_back(c3);
                    col[l++] = temp;
                }
				}
		  }
		  
		  init();
    }

    bool scroll(string_view in) {
        if (in == "q") exit(0);
        if (in == "w") start_row = max(1LL, start_row - 10);
        else if (in == "d") start_col = min(C, start_col + 10);
        else if (in == "a") start_col = max(1LL, start_col - 10);
        else if (in == "s") start_row = min(R, start_row + 10);
        else return false;
        return true;
    }

	bool assign(string_view cmd) {
		 size_t eq = cmd.find('=');
		 if (eq == string_view::npos) return false;

		 string cell = trim(string(cmd.substr(0, eq)));
		 string value = trim(string(cmd.substr(eq + 1)));

		 auto [row, col_id] = parse_cell_reference(cell);
		 if (row < 1 || row > R || col_id < 1 || col_id > C) return false;

		 if (value.find_first_of("+-*/ABCDEFGHIJKLMNOPQRSTUVWXYZ") != string::npos){
			  // Parse RHS to find all cell references and fill 'right'
			  vector<array<int , 2>> right;
			  static const regex cell_regex(R"(([A-Z]+)([0-9]+))");
			  auto words_begin = sregex_iterator(value.begin(), value.end(), cell_regex);
			  auto words_end = sregex_iterator();

			  for(auto it = words_begin; it != words_end; ++it){
					smatch match = *it;
					string col_str = match[1];
					int r = stoi(match[2]);
					int c = find_col(col_str);
					if(r >= 1 && r <= R && c >= 1 && c <= C) right.push_back({r, c});
			  }
			  
			  int val = evaluate_expression(value);
			  if(val == EVAL_ERROR) return false;
			  
			  //remove previous formula
			  if(rev_graph.find( (row  - 1) * C + col_id ) != rev_graph.end()){
				  for(auto &[x , y] : rev_graph[(row - 1) * C + col_id]){
					  graph[x].erase({(row - 1) * C + col_id , y});
				  }
				  rev_graph.erase((row - 1) * C + col_id);
			  }
			  
			  vis.clear();
			  cycle_check((row - 1) * C + col_id);
			  for(auto &[x , y] : right){
				  if(vis.find((x - 1) * C + y) != vis.end()){
					  cout<<"Circular formula detected : "<<col[y]<<x<<" depends on "<<col[col_id]<<row;
					  cout<<endl;
					  return false;
				  }
			  }
			  
			  sheet[row][col_id] = val;
			  update_dependency((row - 1) * C + col_id);
			  
			  for(auto &[x , y] : right){
					graph[(x - 1) * C + y].insert({(row - 1) * C + col_id , value});
					rev_graph[(row - 1) * C + col_id].insert({(x - 1) * C + y , value});
			  }
			  
		 }
		 else{
			 //remove previous formula
			 if(rev_graph.find( (row  - 1) * C + col_id ) != rev_graph.end()){
				  for(auto &[x , y] : rev_graph[(row - 1) * C + col_id]){
					  graph[x].erase({(row - 1) * C + col_id , y});
				  }
				  rev_graph.erase((row - 1) * C + col_id);
			 }
			 sheet[row][col_id] = stoll(value);
			 update_dependency((row - 1) * C + col_id);
		 }
		 
		 seg_square_sum.update(row , col_id , sheet[row][col_id] * sheet[row][col_id]);
		 seg_sum.update(row , col_id , sheet[row][col_id]);
		 seg_min.update(row , col_id , sheet[row][col_id]);
		 seg_max.update(row , col_id , sheet[row][col_id]);
		 
		 return true;
	}


    void output() {
        output_sheet();
    }

    void output_sheet(){
        cout << setw(5);
        for (int i = start_col; i <= min(start_col + 9, C); ++i)
            cout << col[i] << setw(4);
        cout << '\n';

        for (int i = start_row; i <= min(start_row + 9, R); ++i) {
            cout << i << setw(4);
            for (int j = start_col; j <= min(start_col + 9, C); ++j)
                cout << sheet[i][j] << setw(4);
            cout << '\n';
        }
    }

    void run() {
        string in;
        while (true) {
            getline(cin, in);
            in = trim(in);

            auto start = chrono::high_resolution_clock::now();

            string status = " (ok) > ";
            bool success = true;

            if (in.size() == 1) {
                success = scroll(in);
                if (!success) status = " (unrecognized cmd) > ";
            }
				else if (in.find('=') != string::npos) {
                success = assign(in);
                if (!success) status = " (unrecognized cmd) > ";
            }
				else {
                status = " (unrecognized cmd) > ";
                success = false;
            }

            auto stop = chrono::high_resolution_clock::now();
            chrono::duration<double> duration = stop - start;
            stringstream ss;
            ss << fixed << setprecision(1) << "[" << duration.count() << "]" << status;

            output();
            cout << ss.str();
            cout << flush;
        }
    }
};

int32_t main(int argc, char* argv[]) {
    ios::sync_with_stdio(0);
    cin.tie(0);

    if (argc != 3) {
        cerr << "Usage: ./sheet <rows> <columns>\n";
        return 1;
    }

    int row = stoi(argv[1]);
    int col = stoi(argv[2]);

    make_sheet sheet(row, col);
    sheet.output();
    cout << "[0.0] (ok) > " << flush;
    sheet.run();
    return 0;
}