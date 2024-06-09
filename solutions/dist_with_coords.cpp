// Sebastian Galindo

#include <cmath>
#include <math.h>
#include <vector>
#pragma GCC optimize ("O3")
#pragma GCC target ("sse4")
 
#include <bits/stdc++.h>
 
using namespace std;
 
typedef long long ll;
typedef long double ld;
typedef complex<ld> cd;
 
typedef pair<int, int> pi;
typedef pair<ll,ll> pl;
typedef pair<ld,ld> pd;
 
typedef vector<int> vi;
typedef vector<ld> vd;
typedef vector<ll> vl;
typedef vector<pi> vpi;
typedef vector<pl> vpl;
typedef vector<cd> vcd;
 
template<class T> using pq = priority_queue<T>;
template<class T> using pqg = priority_queue<T, vector<T>, greater<T>>;
 
#define forn(i, a) for (int i=0; i<(a); i++)
#define trav(a,x) for (auto& a : x)
#define uid(a, b) uniform_int_distribution<int>(a, b)(rng)
 
#define len(x) (int)(x).size()
#define mp make_pair
#define pb push_back
#define f first
#define s second
#define lb lower_bound
#define ub upper_bound
#define all(x) x.begin(), x.end()
#define ins insert

template<class T> bool ckmin(T& a, const T& b) { return b < a ? a = b, 1 : 0; }
template<class T> bool ckmax(T& a, const T& b) { return a < b ? a = b, 1 : 0; }

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

void __print(int x) {cerr << x;}
void __print(long x) {cerr << x;}
void __print(long long x) {cerr << x;}
void __print(unsigned x) {cerr << x;}
void __print(unsigned long x) {cerr << x;}
void __print(unsigned long long x) {cerr << x;}
void __print(float x) {cerr << x;}
void __print(double x) {cerr << x;}
void __print(long double x) {cerr << x;}
void __print(char x) {cerr << '\'' << x << '\'';}
void __print(const char *x) {cerr << '\"' << x << '\"';}
void __print(const string &x) {cerr << '\"' << x << '\"';}
void __print(bool x) {cerr << (x ? "true" : "false");}
 
template<typename T, typename V>
void __print(const pair<T, V> &x);
template<typename T>
void __print(const T &x) {int f = 0; cerr << '{'; for (auto &i: x) cerr << (f++ ? ", " : ""), __print(i); cerr << "}";}
template<typename T, typename V>
void __print(const pair<T, V> &x) {cerr << '{'; __print(x.first); cerr << ", "; __print(x.second); cerr << '}';}
void _print() {cerr << "]\n";}
template <typename T, typename... V>
void _print(T t, V... v) {__print(t); if (sizeof...(v)) cerr << ", "; _print(v...);}
#ifdef DEBUG
#define debug(x...) cerr << "\e[91m"<<__func__<<":"<<__LINE__<<" [" << #x << "] = ["; _print(x); cerr << "\e[39m" << endl;
#else
#define debug(x...)
#endif
 

const int MOD = 1000000007;
const char nl = '\n';
const int MX = 100001; 

vpl pnts;

// A* variant
struct BidirectionalDijkstra {
    
    vector< vpl > Greverse, G;
    vl dist, distReverse, parent, parentReverse, realDist, realDistR;
    vector<bool> vis, visReverse;
    const ll INF = 1e17;
    ll finalDistance, n;
    vl path;

    BidirectionalDijkstra(vector<vpl> &adj, ll n) {
        G = adj;
        this->n = n;
        Greverse.resize(n+5); reverseGraph();
    }

    void init() {   
        dist.assign(n+5, INF); distReverse.assign(n+5, INF);
        parent.assign(n+5, -1); parentReverse.assign(n+5, -1);
        vis.assign(n+5, false); visReverse.assign(n+5, false);
        realDist.assign(n+5, INF); realDistR.assign(n+5, INF);
    }

    void compute(ll S, ll T) {
        init();
        finalDistance = INF;
        pqg< pl > q, qReverse;
        dist[S] = 0; distReverse[T] = 0;
        realDist[S] = 0; realDistR[T] = 0;
        q.push({ 0, S }); qReverse.push({0, T});
        while (len(q) || len(qReverse)) {

            if (len(q) > 0) {
            auto v = q.top().second; q.pop();
            for (auto [u, len_u]: G[v]) {
                auto newLen = len_u - pf(v, S, T) + pf(u, S, T);
                if (dist[u] > dist[v] + newLen) {
                    dist[u] = dist[v] + newLen;
                    realDist[u] = realDist[v] + len_u;
                    parent[u] = v;
                    q.emplace(make_pair(dist[u], u));
                }
            }
            vis[v] = true;

            if (visReverse[v]) {
                buildPath(S, T);
                break;
            }
            }

            if (len(qReverse) > 0) {

            auto vR = qReverse.top().second; qReverse.pop();

            for (auto [u, len_u]: Greverse[vR]) {
                auto newLen = len_u - pr(vR, S, T) + pr(u, S, T);
                if (distReverse[u] > distReverse[vR] + newLen) {
                    distReverse[u] = distReverse[vR] + newLen;
                    realDistR[u] = realDistR[vR] + len_u;
                    parentReverse[u] = vR;
                    qReverse.emplace(make_pair(distReverse[u], u));
                }
            }

            visReverse[vR] = true;

            if (vis[vR]) {
                buildPath(S, T);
                break;
            }
            }
        }    
    }

    void reverseGraph() {
        forn(i, n) { 
            for (auto [u, len_u]: G[i+1]) {
                Greverse[u].pb({i+1, len_u}); 
            }
        }
    }

    void buildPath(ll S, ll T) {
        ll uBest = -1, tempDist = INF;
        forn(i, n) {
            ll u = i+1;
            if (vis[u] || visReverse[u]) {
                if (realDist[u] + realDistR[u] < tempDist) {
                    uBest = u;
                    finalDistance = dist[u] + distReverse[u];
                    tempDist = realDist[u] + realDistR[u];
                }
            }
        }

        finalDistance = tempDist;

        ll last = uBest;
        while (last != S) { path.pb(last); last = parent[last]; }
        reverse(all(path));
        last = uBest;
        while (last != T) { last = parentReverse[last]; path.pb(last); }
    }

    ll pf(ll vertex, ll S, ll T) {
        return (piFunF(vertex, T)-piFunR(vertex, S))/2;
    }

    ll pr(ll vertex, ll S, ll T) {
        return -pf(vertex, S, T);
    }

    ll piFunF(ll vertex, ll T) {
        return (sqrt((pnts[vertex].f-pnts[T].f)*(pnts[vertex].f - pnts[T].f) + (pnts[vertex].s-pnts[T].s)*(pnts[vertex].s-pnts[T].s)));
    }

    ll piFunR(ll vertex, ll S) {
        return (sqrt((pnts[vertex].f-pnts[S].f)*(pnts[vertex].f - pnts[S].f) + (pnts[vertex].s-pnts[S].s)*(pnts[vertex].s-pnts[S].s))); 
    }
};

struct Astar {
    const ll INF = 1e17;
    vector<vpl> adj;
    ll n, finalDistance = INF;

    Astar(vector<vpl> &adj, ll n) {
        this->adj = adj;
        this->n = n;
    }

    void compute(ll S, ll T) {
        finalDistance = INF;
        vl dist(n+5, INF), parent(n+5, -1);
        pqg<pl> q;
        dist[S] = 0; q.push({0, S});
        while (len(q)) {
            auto [dist_v, v] = q.top(); q.pop();
            if (dist_v > dist[v]) continue;

            for (auto [u, len_u]: adj[v]) {
                auto newLen = len_u - piFun(v, T) + piFun(u, T);
                if (dist[u] > dist[v] + newLen) {
                    dist[u] = dist[v] + newLen;
                    parent[u] = v;
                    q.push({dist[u], u});
                }
            }
        }
        if (dist[T] != INF) finalDistance = dist[T] + piFun(S, T);
    }

    ll piFun(ll v, ll T) {
        return (ll)(sqrt((pnts[v].f-pnts[T].f)*(pnts[v].f-pnts[T].f) + (pnts[v].s-pnts[T].s)*(pnts[v].s-pnts[T].s)));
    }
};

void solve() {
 
    //freopen("out.txt", "w", stdout);
    ll n, m; cin >> n >> m;
    pnts.resize(n+5);
    forn(i, n) cin >> pnts[i+1].f >> pnts[i+1].s;
    vector<vpl> adj(n+5);
    forn(i, m) {
        ll u, v, l; cin >> u >> v >> l;
        adj[u].pb({v, l});
    }

    BidirectionalDijkstra g(adj, n);
//    Astar g(adj, n);
    ll q; cin >> q;
    while(q--) {
        ll u, v; cin >> u >> v; g.compute(u, v);
        cout << (g.finalDistance == g.INF ? -1 : g.finalDistance) << nl;
    }
}
 
int main() {
    cin.tie(0)->sync_with_stdio(0); 
    cin.exceptions(cin.failbit);
 
    int T = 1;
    while(T--) {
        solve();
    }
 
	return 0;
}
 

