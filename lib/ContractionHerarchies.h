struct ContractionHerarchies {
    
    const ll INF = 1e17;
    vector< vpl > G, Gr;
    vector< set<ll> > in, out;
    vl rank, importance, cn, L, sc;
    map< string, ll > w;
    ll n;

    struct Shortcut {
        ll u, v, l;

        Shortcut(ll a, ll b, ll w) : u(a), v(b), l(w) {};
    };

    vector< vector<Shortcut> > shortcuts;

    ContractionHerarchies(vector< vpl > &adj, ll n) {
        G = adj;
        this->n = n;
        rank.assign(n+5, -1);
        shortcuts.resize(n+5);
        importance.assign(n+5, 0);
        Gr.resize(n+5);
        cn.assign(n+5, 0); L.assign(n+5, 0); sc.assign(n+5, 0);
        in.resize(n+5); out.resize(n+5);
        getInOutDegree();
        contractNodes();
        reverseGraph();
    }

    void reverseGraph() {
        forn(i, n) for (auto [v, l]: G[i+1]) Gr[v].pb({i+1, l});
    }

    void contractNodes() {
        pqg< pl > q; // { Importance, node }
        forn(i, n) {
            computeShortCuts(i+1);
            q.push({0, i+1});
        }
        int _curr = 0, _rank = 0;
        while (len(q)) {
            ll _v = q.top().s; q.pop();
            if (_curr == n) {
                _curr = 0;
                rank[_v] = _rank;
                _rank++;
                computeContractNode(_v);
                continue;
            }

            computeImportance(_v);
            if (importance[_v] <= q.top().f) {
                _curr = 0;
                rank[_v] = _rank;
                _rank++;
                computeContractNode(_v);
            } else {
                _curr++;
                q.push({importance[_v], _v});
            }
        }
    }

    void getInOutDegree() {
        forn(i, n) {
            for (auto [v, len_v]: G[i+1]) {
                out[i+1].insert(v); in[v].insert(i+1);
                w[to_string(i+1)+to_string(v)] = len_v;
            }
        }
    }

    void computeContractNode(ll _v) {
        for (auto [u, v, l]: shortcuts[_v]) {
            G[u].push_back({v, l});
            in[v].insert(u); out[u].insert(v);
            w[to_string(u)+to_string(v)] = l;
        }

        for (auto _a: in[_v]) {
            L[_a] = max(L[_a], L[_v]+1);
            cn[_a]++;
        }

        for (auto _a: out[_v]) cn[_a]++;
    }
    
    void computeImportance(ll v) {
        // Edge Diff
        ll ed = len(shortcuts[v]) - len(in[v]) - len(out[v]);
        importance[v] = ed + cn[v] + L[v] + sc[v];
    }

    void computeShortCuts(ll v) {
        ll _maxIn = -1, _maxOut = -1;
        for (auto _a: in[v]) _maxIn = max(_maxIn, w[to_string(_a)+to_string(v)]);
        for (auto _a: out[v]) _maxOut = max(_maxOut, w[to_string(v) + to_string(_a)]);

        for (auto _a: in[v]) Dijkstra(_a, v, _maxIn+_maxOut);
        set<ll> neighShorts;
        for (auto [_q, _r, _l]: shortcuts[v]){
            neighShorts.insert(_q); neighShorts.insert(_r);
        }
        sc[v] = len(neighShorts);
    }

    void Dijkstra(ll S, ll C, ll thrhld) {
        vl _dist(n+5, INF);
        pqg<pl> _q;
        _q.push({0, S});
        _dist[S] = 0;
        while (len(_q)) {
            auto [dist_s, _s] = _q.top(); _q.pop();
            if (dist_s > _dist[_s]) continue;

            for (auto [_u, len_u]: G[_s]) {
                if (_u == C) continue;
                if (_dist[_u] > _dist[_s] + len_u) {
                    _dist[_u] = _dist[_s] + len_u;
                    ll len_S_u = w[to_string(S)+to_string(C)] + w[to_string(C)+to_string(_u)];
                    if (out[C].count(_u) && len_S_u < _dist[_u]) {
                        shortcuts[C].pb(Shortcut(S, _u, len_S_u));
                        continue;
                    }
                    if (_dist[_u] > thrhld) continue;
                    if (!out[C].count(_u)) _q.push({_dist[_u], _u});
                }
            }
        }

        for (auto _y: out[C]) {
            if (_dist[_y] != INF) continue;
            ll len_S_y = w[to_string(S) + to_string(C)]+w[to_string(C)+to_string(_y)];
            shortcuts[C].pb(Shortcut(S, _y, len_S_y));
        }
    }

    ll query(ll S, ll T) {
        ll estimate = INF;
        vl dist(n+5, INF), distR(n+5, INF);
        vector<bool> vis(n+5, false), visR(n+5, false);
        pqg< pl > q, qR;
        dist[S] = 0; distR[T] = 0;
        q.push({0, S}); qR.push({0, T});

        while (len(q) || len(qR)) {
            if (len(q) > 0) {
                auto _v = q.top().s; q.pop();
                if (dist[_v] <= estimate) {
                    for (auto [_u, len_u]: G[_v]) {
                        if (dist[_u] > dist[_v] + len_u && rank[_u] > rank[_v]) {
                            dist[_u] = dist[_v] + len_u;
                            q.push({dist[_u], _u});
                        }
                    }

                    vis[_v] = true;
                }
                if (visR[_v] && dist[_v] + distR[_v] < estimate) {
                    estimate = dist[_v] + distR[_v];
                }
            }

            if (len(qR) > 0) {
                auto _v = qR.top().s; qR.pop();
                if (distR[_v] <= estimate) {
                    for (auto [_u, len_u]: Gr[_v]) {
                        if (distR[_u] > distR[_v] + len_u && rank[_u] > rank[_v]) {
                            distR[_u] = distR[_v] + len_u;
                            qR.push({distR[_u], _u});
                        }
                    }
                }

                visR[_v] = true;
                if (vis[_v] && dist[_v] + distR[_v] < estimate) {
                    estimate = dist[_v] + distR[_v];
                }

            }
        }

        return estimate;
    }

};
