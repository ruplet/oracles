template <class... T> void g(T... t) {g(t..., t... );} 
int main() {g(0);}
