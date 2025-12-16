#include <iostream>

using namespace std;

int main () { 
    int x = 0;
    int y = 1;
    int sel = 1;
    for (int i = 0; i < 10; i++) {
        if (sel == 1) { 
            x = x + y;
            sel = 2;
            cout << x << endl; 
        }
        else { 
            y = x + y;
            sel = 1;
            cout << y << endl;
        }
    }
    return 0;
}

// === Code Execution Successful ===

// 1
// 2
// 3
// 5
// 8
// 13
// 21
// 34
// 55
// 89
