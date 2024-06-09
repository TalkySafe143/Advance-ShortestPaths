struct BidirectionalDijkstra {
    
    vector< vpl > Greverse, G;
    vl dist, distReverse, parent, parentReverse;
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
    }

    void compute(ll S, ll T) {
        init();
        finalDistance = INF;
        pqg< pl > q, qReverse;
        dist[S] = 0; distReverse[T] = 0;
        q.push({ 0, S }); qReverse.push({0, T});
        while (len(q) || len(qReverse)) {

            if (len(q) > 0) {
            auto v = q.top().second; q.pop();
            for (auto [u, len_u]: G[v]) {
                if (dist[u] > dist[v] + len_u) {
                    dist[u] = dist[v] + len_u;
                    parent[u] = v;
//                    q.push({dist[u], u});
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
                if (distReverse[u] > distReverse[vR] + len_u) {
                    distReverse[u] = distReverse[vR] + len_u;
                    parentReverse[u] = vR;
                    //qReverse.push({ distReverse[u], u });
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
        ll uBest = -1;

        forn(i, n) {
            ll u = i+1;
            if (vis[u] || visReverse[u]) {
                if (dist[u] + distReverse[u] < finalDistance) {
                    uBest = u;
                    finalDistance = dist[u] + distReverse[u];
                }
            }
        }

        ll last = uBest;
        while (last != S) { path.pb(last); last = parent[last]; }
        reverse(all(path));
        last = uBest;
        while (last != T) { last = parentReverse[last]; path.pb(last); }
    }
};
