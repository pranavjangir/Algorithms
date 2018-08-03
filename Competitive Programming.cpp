
//************************************ Dijkstra Variant: Doing DIJK along with finding the number of shortest path possible to a point************//
for (int i=1;i<=n;i++)
 dist[i]=1e16;
ways[1]=1;
dist[1]=0;

for (int i=1;i<=n;i++)
{
 sett.insert(make_pair(dist[i],i));
}

for (int iter=1;iter<=n;iter++)
{
 it=sett.begin();
 qv=(*it).second;
 qcost=(*it).first;
 sett.erase(it);
 for (int i=0;i<g[qv].size();i++)
 {
  tv=g[qv][i].first;
  tcost=g[qv][i].second+qcost;
  if (tcost>dist[tv])continue;
  if (tcost==dist[tv]){ways[tv]+=ways[qv];continue;}
  sett.erase(make_pair(dist[tv],tv));
  dist[tv]=tcost;
  ways[tv]=ways[qv];
  sett.insert(make_pair(dist[tv],tv));
 }
}

wagasufesi@geekforex.com

//******************************************************Find cycles count and sizes in directed graph**************************************//

void dfs2(ll s)
{
        cycles[cc]++;
        vis[s] = 3;
        if(vis[a[s]] == 3) return;

        dfs2(a[s]);
}
void dfs(ll s)
{
        vis[s] = 1;
        if(vis[a[s]] == 0)
        {
                dfs(a[s]);
        }else if(vis[a[s]] == 1)
        {
                cycles.push_back(0);
                dfs2(a[s]);
                cc++;
        }else
        {
                vis[s] = 2;
                return;
        }
        vis[s] = 2;
}
//*******************************************************Modified Sieve***********************************************************//
bool prime[100100];
ll s[100100];
void sieve()
{
        memset(prime,true,sizeof prime);
        prime[1] = prime[0] = false;
        //s[1] = 1;
        for(ll i=2;i <= 100005;i++)
        {
                if(prime[i])
                {
                        s[i] = i;
                        for(ll j = 2*i ; j <= 100005 ; j += i)
                        {
                                prime[j] = false;
                                s[j] = i;
                        }
                }
        }
}
//**********************************************MY seg tree*********************************************************************//
inline ll left(ll x){return x<<1;}
inline ll right(ll x){return (x<<1)+1;}
void build(ll id,ll l,ll r)
{
        if(l == r)
        {
                tree[id] = b[l]; return;
        }
        ll mid = (l + r)/2;
        build(left(id) , l , mid);
        build(right(id) , mid + 1, r);

        tree[id] = tree[left(id)] + tree[right(id)];
}

void upd(ll id , ll x, ll l, ll r,ll val)
{
        if(l == r)
        {
                tree[id] = val; return;
        }
        ll mid = (l + r)/2;
        if(x <= mid)
                upd(left(id) , x , l ,mid , val);
        else{
                upd(right(id) , x , mid + 1, r, val);
        }

        tree[id] = tree[left(id)] + tree[right(id)];
}

ll qry(ll id ,ll x ,ll y,ll l ,ll r)
{
        ll mid = (l+r) >> 1;
        if(x > r || y < l) return INVAL;
        if(l >= x && r <= y) return tree[id];
        ll X = qry(left(id) , x , y , l , mid);
        ll Y = qry(right(id) , x , y , mid+1 , r);
        if(X == INVAL) return Y;
        else if(Y == INVAL) return X;
        else {
                return X+Y;
        }

}
//***********************************************************************************************************************************//
EXTENDED EUCLIDEAN ALGORITHM : 

// returns gcd and also changes the values of global variables x and y to bezemout's coefficients!

long long gcd(long long a,long long b,long long& x,long long &y)
{
        if (a==0)
        {
                x=0,y=1;return b;
        }
        long long x1,y1;
        long long d=gcd(b%a,a,x1,y1);
        x=y1-b/a*x1;
        y=x1;
        return d;
}
//**************************************************************************************************************************************//
SIEVE FOR INCLUSION EXCLUSION PRINCIPLE:

void sieve()
{
        memset(prime, true , sizeof prime);
        for(ll i=0;i<=1000002;i++) sign[i] = 1;
        prime[1] = prime[0] = false;
        for(ll i=2;i<=1000002;i++)
        {
                if(prime[i]){

                        for(ll j=i;j<=1000002;j+=i){
                                ll x = j/i;
                                if(x%i == 0) sign[j] = 0;
                                else sign[j] = sign[j]*-1;
                                prime[j] = false;
                        }
                }
        }
}
//******************************************************************************************************************************************//
//ME
ll ME(ll x,ll nn,ll M)
{
    ll result=1;
    while(nn>0)
    {
        if(nn % 2 ==1)
            result=(result * x)%M;
        x=(x*x)%M;
        nn=nn/2;
    }
    return result;
}
//*******************************************************************************************************************************************//
// Merge-sort
void ms(ll s , ll e)
{
        if(s >= e) return;
        if((e == (s+1))) return;
        ll mid = (s + e)/2;
        ms(s , mid);
        ms(mid,e );
        vector<ll> t;
        ll p=s; ll q = mid;
        while((p<mid)&&(q<e)){
                if(a[p] <= a[q]){
                        t.push_back(a[p]);
                        p++;
                }else{
                        t.push_back(a[q]);
                        inv += mid-p;
                        q++;
                }
        }
        while(p<mid) t.push_back(a[p++]);
        while(q<e) t.push_back(a[q++]);
        ll i=s;
        for(ll j=0;j<t.size();j++){
                a[i++] = t[j];
        }
}
//********************************************************************************************************************************************//
// Max-Flo implementation O(V^3E)
bool vis[205];
ll p[205];
ll res[205][205];
const ll INF = 1e14;
bool bfs()
{
        memset(vis , false , sizeof vis);
        memset(p , -1 , sizeof p);
        queue<ll> q;
        q.push(s);
        vis[s] = true;
        p[s] = -1;
        while(q.empty() == false)
        {
                ll u = q.front();
                q.pop();
                for(ll i = 1 ; i <= t ; i++)
                {
                        if(!vis[i] && (res[u][i] > 0)) {
                                q.push(i);
                                p[i] = u;
                                vis[i] = true;
                        }
                }
        }
        return vis[t];
}
ll flow()
{
        ll ret = 0;
        while(bfs())
        {
                ll tmp = INF;
                for(ll i = t ; i != s ; i = p[i]) {
                        tmp = min(tmp , res[p[i]][i]);
                }
                for(ll i=t; i != s ; i = p[i]) {
                        res[p[i]][i] -= tmp;
                        res[i][p[i]] += tmp;
                }
                ret += tmp;
        }
        return ret;
}
// fast matrix exponentiation ***************************************************************************//
 // **** modify it a little **********//
void mult(ll a[55][55], ll b[55][55], ll m)
{
	ll d[52][52];
	memset(d,0,sizeof(d));
	for(ll i=0;i<m;i++)
	{
		for(ll j=0;j<m;j++)
		{
			for(ll k=0;k<m;k++)
			{
				d[i][j]+=a[i][k] * b[k][j];
				d[i][j]%=MOD;
			}
		}
	}
	for(ll i=0;i<m;i++)
	{
		for(ll j=0;j<m;j++)
		{
			a[i][j]=d[i][j];
		}
	}
}
ll summ =0;
void EXP(ll t)
{
        for(ll i = 0 ; i < m ; i++) res[i][i] = 1;
        while(t)
        {
                if(t&1){
                        mult(res , a , m);
                }
                mult(a , a , m);
                t = t >> 1;
        }
        for(ll i = 0 ; i<m;i++) {
                for(ll j = 0 ; j < m ; j++)
                {
                        ans[i] = (ans[i] + res[j][i])%MOD;
                }
                summ = (summ + ans[i])%MOD;
        }
}
// ******************************************************************************************************************//
// MATRIX class --- supports , equation , multiplication and fast matrix exponentiation! //
class matrix
{
public:
        vector<vector<ll> > M;
        ll nn , mm;
        matrix()
        {
                nn = mm = 0;
        }
        matrix(ll R , ll C)
        {
                nn = R;
                mm = C;
                M.resize(R);
                for(ll i = 0 ; i < R ; i++)
                {
                        M[i].resize(C);
                }
        }
        void fills(ll i , ll j , ll val)
        {
                M[i][j] = val;
        }
        void equate(matrix B)
        {
                M.clear();
                nn = B.nn;
                mm = B.mm;
                M = B.M;
        }
        matrix operator* (matrix B)
        {
                assert(mm == B.nn);
                matrix ret(nn , B.mm);
                for(ll i = 0 ; i < nn ; i++) for(ll j =0 ; j < B.mm ; j++) ret.M[i][j] = 0;
                        for(ll i=0;i<nn;i++)
                        {
                                for(ll j=0;j<B.mm;j++)
                                {
                                        for(ll k=0;k<mm;k++)
                                        {
                                                ret.M[i][j] += M[i][k] * B.M[k][j];
                                                ret.M[i][j] %= MOD;
                                        }
                                }
                        }
                        return ret;
        }
        matrix EXP(ll x)
        {
                assert(nn == mm);
                matrix A(nn , mm);
                for(ll i = 0 ; i < nn ; i++)
                {
                        for(ll j = 0; j < mm ; j++)
                                A.M[i][j] = M[i][j];
                }
                matrix ret(nn , nn);
                for(ll i = 0 ; i < nn ; i++){
                                ret.M[i][i] = 1;
                }
                while(x)
                {
                        if(x&1){
                                ret.equate(ret*A);
                        }
                        A.equate(A*A);
                        x = x / 2;
                }
                return ret;
        }
};
//***************************************************************************************************//
C++ tree :

#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define pb push_back
typedef long long ll;
using namespace __gnu_pbds;

typedef tree<int, null_type, less<int>, rb_tree_tag,
             tree_order_statistics_node_update>
    boxx;
// use the name boxx to now refer to this new data structure!
//******************************************************************************************************//
Z - Algorithm :

vector<ll> Z(string K)
{
        ll l = 0;
        ll r = 0;
        vector<ll> z;
        z.resize(K.length());
        for(ll i=1;i<K.length();i++)
        {
                if(i <= r && i >= l) {
                        z[i] = min(r - i + 1 , z[i-l]);
                }
                while(i + z[i] < K.length() && K[z[i]] == K[i + z[i]]) ++z[i];
                if(i + z[i] - 1 > r) {
                        l = i;
                        r = i + z[i] - 1;
                }
        }
        return z;
}
//********************************************************************************************************//
Mod Utilities :

inline ll _add(ll a, ll b){
	a += b;
	if(a >= MOD)
		a -= MOD;
	return a;
}

inline ll _sub(ll a, ll b){
	a -= b;
	if(a < 0)
		a += MOD;
	return a;
}

inline ll _mult(ll a, ll b){
	return (1LL * a * b) % MOD;
}
//*********************************************************************************************************//
Dynamic Segment tree node :-

class node
{
public:
        ll l , r , val;
        node* lft;
        node* rgt;
        node()
        {

        }
        node(ll x , ll y)
        {
                l = x; r = y; val = 0;
                lft = NULL;
                rgt = NULL;
        }
        void upd(ll id, ll nval)
        {
                if(l == r)
                {
                        val = nval; return;
                }
                ll mid = (l + r)>>1;
                if(id <= mid) {
                        if(lft == NULL) {
                                lft = new node(l , mid);
                        }
                        lft->upd(id , nval);
                }
                else {
                        if(rgt == NULL) {
                                rgt = new node(mid+1 , r);
                        }
                        rgt->upd(id , nval);
                }
                val = 0;
                if(lft) val = max(val , lft->val);
                if(rgt) val = max(val , rgt->val);


        }
        ll qry(ll x , ll y)
        {
                if(l > y || r < x) return 0;
                if(l >= x && r <= y) return val;
                ll mid = (l + r) >> 1;
                ll ret = 0;
                if(lft) ret = max(ret , lft->qry(x , y));
                if(rgt) ret = max(ret , rgt->qry(x , y));
                return ret;
        }

};
//********************************************************************************************************//
Minimum Cost Max Flow :- (For maxflow in an augumented path = 1)

void add_edge(ll a , ll b , ll c , ll d)
{
        frm[ec] = a;
        to[ec] = b;
        cap[ec] = c;
        cost[ec] = d;
        g[a].pb(ec);
        ec++;
        frm[ec] = b;
        to[ec] = a;
        cap[ec] = 0;
        cost[ec] = -1*d;
        g[b].pb(ec);
        ec++;
}
ll p[505];
bool bfs()
{
        //queue<ll> q;
        for(ll i = 0 ; i <= n+n+1 ; i++) d[i] = inf;
        q[0] = s;
        d[s] = 0;
        ll ql=0;
        ll qr=1;
        while(ql < qr)
        {
                ll u = q[ql++];
                //q.pop();
                for(auto ed : g[u])
                {
                        if(cap[ed] == 0) continue;
                        ll nei = to[ed];
                        if(d[nei] > d[u] + cost[ed]) {
                                d[nei] = d[u] + cost[ed];
                                q[qr++] = nei;
                                p[nei] = ed;
                        }
                }
        }
        return (d[t] < inf);
}
ll mcf()
{
        ll ret = 0;
        while(bfs())
        {
                FLOW++;
                ll j = t;
                while(j != s)
                {
                        ll ed = p[j];
                        --cap[ed];
                        ++cap[ed^1];
                        j = frm[ed];
                }
                ret += d[t];
        }
        return ret;
}
//************************************************************************************************************//
// Bit Tree with lower bound!

class BIT {
public:

        vector<ll> s;
        BIT(int n) : s(n) {}
        void update(int pos, ll dif) {
                for (; pos < s.size(); pos |= pos + 1) s[pos] += dif;
        }
        ll query(int pos) {
                ll res = 0;
                for (; pos > 0; pos &= pos - 1) res += s[pos-1];
                return res;
        }
        int lowerB(ll sum) {
                if (sum <= 0) return -1;
                int pos = 0;
                for (int pw = 1 << 25; pw; pw >>= 1) {
                                if (pos + pw <= s.size() && s[pos + pw-1] < sum)
                                                        pos += pw, sum -= s[pos-1];
                }
                return pos;
        }
};
//*************************************************************************************************************//
