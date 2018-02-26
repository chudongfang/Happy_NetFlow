#include <stdio.h>
#include <stdlib.h>
#include <queue>
#include <iostream>
#include <cstring>
#include <utility>
#include <cmath>
#include <algorithm>
#include <string>
#include <sstream>
#include <vector>
#include <deque>
#include <map>
#include <set>
#include <stack>
#include <queue>
#include <time.h>
#define MAXN 1200
#define MAXM 24000
// #define __DEBUG
// #pragma comment(linker, "/STACK:102400000,102400000")

using namespace std;
typedef long long ll;
typedef vector<ll> vl;
typedef vector<int> vi;

const int INF = 1e8;
int  city_num    =  50;//城市的数目
int  unit_num    =  10;//种群中个体的数目
int  probability =  70;//变异概率
int  genmax      = INF;//最大产生代数
int  group_num   = 1;//产生种群数量
int  ch_num      = 10;
typedef struct individual //一个个体
{
    vi  path;
    set<int>  yes_point;
    int lenth;         //路径的长度
    int weight;
    int num_f;
}INDI;


bool cmp(INDI xx,INDI yy)
{
    return xx.lenth < yy.lenth;
}

bool cmp_w(INDI xx,INDI yy)
{
    return xx.weight < yy.weight;
}

INDI cross_tm,cross_tf;
vector<INDI> cross_t;
typedef struct unit//一个种群
{
    vector<INDI> group; //数组存储个体
    INDI best;            //最优个体
    int  best_gen;        //最优个体所在的代数
    int  cur_gen;         //种群当前的代数
}UNIT;






void init();
void addEdge(int u, int v, int cap, int cost);
bool spfa(int st, int en);
int minCostMaxflow(int st, int en, int &cost);
bool spfa_r(int st, int en);
int minCostMaxflow_r(int st, int en, int &cost);
int get_re(vi a,int size);
int print_re(vi a,int size);
int get_re_zwk(vi a);
//1.初始化t←0进化代数计数器；genmax是最大进化代数；随机生成unit_num个个体作为初始群体P(t)；
void init_();
//2.个体评价
void assess();
//3.选择运算 将选择算子作用于群体
void choose(int gen);
//4.交叉运算 将交叉算子作用于群体，保留较优个体，淘汰较差个体
void cross();
//5.变异运算 将变异算子作用于群体，并通过以上运算得到下一代群体p(t+1)
void mutation();
//总调用函数，决定一个种群的进化
void sovel();
//子模块
void  cross_once(int father,int mother);
void mutation_one(int x);



//创建一个种群
UNIT  Group;
//储存每个种群进化的结果
vector<INDI>  bestsovel;









int  n,edge_num,m ,val_f;
int _u,_v,val,_e,t,re;
int ed,sr;



//edge number
int uu[MAXM];
int vv[MAXM];
int ee[MAXM];
int vall[MAXM];

//point number
int u1[MAXN];
int e1[MAXN];
int xf[MAXN];

time_t t_start, t_end;
int use_time=80;
vi road;
vi froad;
int fff_road[MAXN];
int fl=0;
string tt1;
string res;



char a[50];
int edge_map[MAXM];

INDI t_main;


struct Edge
{
    int to, next, cap, flow, cost;
    Edge(int _to = 0, int _next = 0, int _cap = 0, int _flow = 0, int _cost = 0) :
            to(_to), next(_next), cap(_cap), flow(_flow), cost(_cost) {}
}edge[MAXM];


struct MinCostMaxFlow
{

    int INFF = 1e9;
    int head[MAXM], tot;//
    int cur[MAXM];//
    int dis[MAXM];
    bool vis[MAXM];
    stringstream s11;
    string rree;
    string tt_;
    vi road_t;
    int ss, tt, N;//源点、汇点和点的总个数（编号是0~N-1）,不需要额外赋值，调用会直接赋值
    int min_cost, max_flow;
    stack<int> S,SR;
    int resnum = 0;
    int ff;
    int flow_min  =  INFF;



    void init()
    {
        tot = 0;
        memset(head, -1, sizeof(head));
    }
    void addedge(int u, int v, int cap, int cost)
    {
        edge[tot] = Edge(v, head[u], cap, 0, cost);
        head[u] = tot++;
        edge[tot] = Edge(u, head[v], 0, 0, -cost);
        head[v] = tot++;
    }
    int aug(int u, int flow)
    {
        if (u == tt) return flow;
        vis[u] = true;
        for (int i = cur[u];i != -1;i = edge[i].next)
        {
            int v = edge[i].to;
            if (edge[i].cap > edge[i].flow && !vis[v] && dis[u] == dis[v] + edge[i].cost)
            {
                int tmp = aug(v, min(flow, edge[i].cap - edge[i].flow));
                edge[i].flow += tmp;
                edge[i ^ 1].flow -= tmp;
                cur[u] = i;
                if (tmp)return tmp;
            }
        }
        return 0;
    }
    bool modify_label()
    {
        int d = INF;
        for (int u = 0;u < N;u++)
            if (vis[u])
                for (int i = head[u];i != -1;i = edge[i].next)
                {
                    int v = edge[i].to;
                    if (edge[i].cap>edge[i].flow && !vis[v])
                        d = min(d, dis[v] + edge[i].cost - dis[u]);
                }
        if (d == INF)return false;
        for (int i = 0;i < N;i++)
            if (vis[i])
            {
                vis[i] = false;
                dis[i] += d;

            }
        return true;
    }
    /*
    * 直接调用获取最小费用和最大流
    * 输入: start-源点，end-汇点，n-点的总个数（编号从0开始）
    * 返回值: pair<int,int> 第一个是最小费用，第二个是最大流
    */
    pair<int, int> mincostmaxflow(int start, int end, int n)
    {
        ss = start, tt = end, N = n;
        min_cost = max_flow = 0;
        for (int i = 0;i < n;i++)dis[i] = 0;
        while (1)
        {
            for (int i = 0;i < n;i++)cur[i] = head[i];
            while (1)
            {
                for (int i = 0;i < n;i++) vis[i] = false;
                int tmp = aug(ss, INF);
                if (tmp == 0)break;
                max_flow += tmp;
                min_cost += tmp*dis[ss];
            }
            if (!modify_label())break;
        }
        return make_pair(min_cost, max_flow);
    }





    void print_one_road(int x,int minn)
    {
        if(ff) return ;
        if(x==tt)
        {
            flow_min = minn;
            SR = S;
            ff = 1;
            return ;
        }
        for (int i = head[x];i != -1;i = edge[i].next)
        {
            if(i%2)
                continue;
            int v = edge[i].to;

            if (edge[i].flow > 0)
            {
                S.push(i);
                print_one_road(v,min(minn,edge[i].flow));
                S.pop();
                break;
            }
        }
        return ;
    }
    void print_road()
    {
        int tedge;
        rree.clear();
        flow_min=INFF;
        ff = 0;

        print_one_road(ss,INFF);

        while(flow_min!=INFF)
        {
            road_t.clear();
            while(!SR.empty())
            {
                tedge = SR.top();
                edge[tedge].flow-=flow_min;
                road_t.push_back(edge[tedge].to-1);
                SR.pop();
            }

            for(int i=road_t.size()-1;i>=1;i--)
            {
                s11.clear();
                s11<< road_t[i];
                s11>>tt_;
                rree += tt_;
                rree+=" ";
            }
            s11.clear();
            s11<< edge_map[road_t[1]]-1;
            s11>>tt_;
            rree += tt_;
            rree+=" ";

            s11.clear();
            s11<< flow_min;
            s11>>tt_;
            rree += tt_;
            rree+="\n";

            while(!S.empty())
                S.pop();

            resnum++;
            ff = 0;
            flow_min=INFF;
            road_t.clear();
            print_one_road(ss,INFF);

        }
    }

    int get_resnum()
    {
        return resnum;
    }

    string get_rree()
    {
        return rree;
    }

}solve;
















void deploy_server(char * topo[MAX_EDGE_NUM], int line_num,char * filename)
{
    t_start = time(NULL) ;
    srand(time(0));

    stringstream ss;
    ss.clear();
    for(int i=0;i<line_num;i++)
    {
        ss<<topo[i];
    }

    ss >> n>>edge_num>>m;
    ss >> val_f;
    city_num = n;

    if(n>600)
    {
        unit_num    = 20;//种群中个体的数目
        probability = 70;//变异概率
    }
    else if(n>400)
    {
        unit_num    = 30;//种群中个体的数目
        probability = 84;//变异概率
    }
    else if(n>=250)
    {
        unit_num    = 30;//种群中个体的数目
        probability = 100;//变异概率
    }


    ed = n+1;
    sr = 0;

    for(int i=0;i<edge_num;i++)
    {
        ss>> uu[i] >> vv[i] >> ee[i] >> vall[i];
    }


    for(int i=0;i<m;i++)
    {
        ss >> xf[i] >> u1[i] >> e1[i];
        fl += e1[i];
        fff_road[u1[i]] = 1;
        // t_main.yes_point.insert(u1[i]+1);
        edge_map[u1[i]] = xf[i]+1;
    }

    for(int i=0;i<n;i++)
    {
        if(fff_road[i])
            froad.push_back(1);
        else
            froad.push_back(0);
    }


    t_main.path = froad;
    t_main.lenth = fl + m*val_f;
    t_main.num_f = m;
    bestsovel.push_back(t_main);




    sovel();
    bestsovel.push_back(Group.best);

    sort(bestsovel.begin(),bestsovel.end(),cmp);


#ifdef __DEBUG

    printf("最优解：");
    for(int i=0;i<city_num;i++)
    printf("%4d",Group.best.path[i]);
    cout<<endl<<"all::"<<fl+val_f*m<<"最优值："<<Group.best.lenth<<"*****save "<<fl+val_f*m -Group.best.lenth<<endl;
    cout <<"*****************************"<<endl;

#endif





    tt1.clear();
    res.clear();

    print_re(bestsovel[0].path,city_num);

    ss.clear();
    tt1.clear();
    ss<<solve.get_resnum();
    ss>>tt1;
    tt1 += '\n';
    tt1 += '\n';
    res = tt1+solve.get_rree();


    char * topo_file = (char *)res.c_str();
    write_result(topo_file, filename);
}










int get_re_zwk(vi a)
{


    solve.init();
    for(int i=0;i<edge_num;i++)
    {
        //把每个节点向前加1
        solve.addedge(uu[i]+1,vv[i]+1,ee[i],vall[i]);
        solve.addedge(vv[i]+1,uu[i]+1,ee[i],vall[i]);
    }

    for(int i=0;i<m;i++)
    {
        solve.addedge(u1[i]+1,ed,e1[i],0);
    }


    for(int i=0;i<a.size();i++)
    {
        if(a[i])
        {
            solve.addedge(sr,i+1,INF,0);
        }
    }

    pair<int, int> an = solve.mincostmaxflow(sr, ed, ed+1);

    if(fl == an.second)
    {
        return an.first;
    }
    else
    {
        return -1;
    }
}


int print_re(vi a,int size)
{

    solve.init();
    for(int i=0;i<edge_num;i++)
    {
        //把每个节点向前加1
        solve.addedge(uu[i]+1,vv[i]+1,ee[i],vall[i]);
        solve.addedge(vv[i]+1,uu[i]+1,ee[i],vall[i]);
    }

    for(int i=0;i<m;i++)
    {
        solve.addedge(u1[i]+1,ed,e1[i],0);
    }
    for(int i=0;i<a.size();i++)
    {
        if(a[i])
        {
            solve.addedge(sr,i+1,INF,0);
        }
    }

    pair<int, int> an = solve.mincostmaxflow(sr, ed, ed+1);

    solve.print_road();
    if(fl == an.second)
    {
        return an.first;
    }
    else
    {
        return -1;
    }
}






//对一个种群进行求解。
void sovel()
{

    init_();
    time_t deploy_server_t   =  0;
    int    deploy_server_ff  =  0;


    for(int i=1;i <= genmax ; i++) //种群繁杂代数
    {

        assess();               //评估
        choose(Group.cur_gen);  //找最优个体
        cross();                //交叉,优胜劣汰，保留较优个体，淘汰较差个体
        mutation();             //变异
        t_end = time(NULL) ;
        if(!deploy_server_ff)
        {
            deploy_server_t = difftime(t_end,t_start);
            deploy_server_ff = 1;
        }

        if(difftime(t_end,t_start)>=87-deploy_server_t)
            break;

    #ifdef __DEBUG

        cout <<"time ::" <<difftime(t_end,t_start)<<endl;
        cout <<"the result ::" <<Group.best.lenth<<endl;
    #endif

    }
}



void init_()
{
    INDI t;
    int tt_init_=0;
    int ct_init_=0;

    Group.best.path.clear();
    Group.best.lenth=0x3f3f3f3f;//初始化一个很大的值，便于下面比较
    Group.best_gen=0;//记录产生最好结果的代数
    Group.cur_gen=0;//当前代数为0
    Group.group.clear();//

    Group.group.push_back(t_main);
    Group.group.push_back(t_main);
    Group.group.push_back(t_main);
    Group.group.push_back(t_main);
    Group.group.push_back(t_main);
    //把每一个个体随机初始化
    for(int i=5;i<unit_num;i++)//unit_num个个体
    {
        t.path.clear();
        for(int j=0;j<city_num;j++)
        {
            tt_init_ = rand()%2;
            if(tt_init_)   ct_init_++;
            t.path.push_back(tt_init_);
        }
        t.lenth = INF;
        t.num_f = ct_init_;
        Group.group.push_back(t);
    }
}


//个体评价
void assess()
{
    //计算出每个个体的适应度值，即其路径长度
    for(int k=0;k<unit_num;k++)
    {
        int rel=0;  //#
        rel = get_re_zwk(Group.group[k].path);

        if(rel==-1||rel<0)
        {
            Group.group[k].lenth=INF;
        }
        else
        {
            Group.group[k].lenth=rel+Group.group[k].num_f*val_f;
        }
    }
}


//先进行排序，然后选择出最优解
void choose(int gen)
{
    sort(Group.group.begin(),Group.group.end(),cmp);

    if(Group.best.lenth>Group.group[0].lenth)
    {
        Group.best.lenth = Group.group[0].lenth;
        Group.best.num_f = Group.group[0].num_f;
        Group.best.path  = Group.group[0].path;
        Group.best_gen   = gen;
    }
}




//对一个种群中的个体，按一定方式进行交叉运算,并淘汰掉一部分，保存较优个体
void cross()
{
    int minn,tf,tm,tt;
    cross_t.clear();
    for(int k=0;k<unit_num/2;k++)
    {
        tt = rand()%unit_num;
        minn = rand()%unit_num;
        for(int j=0;j<tt;j++)
        {
            minn = min(minn,rand()%unit_num);
        }
        tf  =  minn;

        tt = rand()%unit_num;
        minn = rand()%unit_num;
        for(int j=0;j<tt;j++)
        {
            minn = min(minn,rand()%unit_num);
        }
        tm =  minn;

        cross_once(tf,tm);

        cross_t.push_back(cross_tf);
        cross_t.push_back(cross_tm);
    }
    Group.group  = cross_t;
}


//交叉两个个体
void  cross_once(int father,int mother)
{
    cross_tf  = Group.group[father];
    cross_tm  = Group.group[mother];
    int l=rand()%city_num;
    int r=rand()%city_num;
    while(l==r)
    {
        l = rand()%city_num;
    }
    if(l>r)
        swap(l,r);
    for(int i=l;i<r;i++)
    {
        if(cross_tf.path[i])
        {
            cross_tf.num_f--;
            cross_tm.num_f++;
        }
        if(cross_tm.path[i])
        {
            cross_tf.num_f++;
            cross_tm.num_f--;
        }
        swap(cross_tf.path[i],cross_tm.path[i]);
    }
    return ;
}



//对一个种群的全部个体都进行变异运算
void mutation()
{
    for(int i=1;i<unit_num;i++)
    {
        mutation_one(i);
    }
}


//对一个个体的变异运算
void mutation_one(int x)
{
    int pro=rand()%100;
    if(pro>probability)
        return ;
    for(int i=0;i<1;i++)
    {
        int first =rand()%city_num;

        if(Group.group[x].path[first])
        {
            Group.group[x].num_f --;
            Group.group[x].path[first] = 0;
        }
        else
        {
            Group.group[x].num_f ++;
            Group.group[x].path[first] = 1;
        }
    }

}








