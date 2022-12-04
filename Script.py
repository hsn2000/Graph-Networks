from os import truncate
import tkinter.font as Font
from tkinter import *
from typing import Any
from collections import defaultdict
import matplotlib.pyplot as plt
import networkx as nx
from networkx.algorithms.assortativity import neighbor_degree
from networkx.algorithms.centrality.current_flow_betweenness import approximate_current_flow_betweenness_centrality
from networkx.algorithms.distance_measures import center
from networkx.algorithms.shortest_paths.dense import floyd_warshall
from networkx.algorithms.tree.branchings import INF
import numpy as np
import sys
from networkx.classes.function import neighbors, number_of_edges
from sys import maxsize

DataList=[]
DataList2=[]
list_of_xaxis = []
list_of_yaxis = []
source=[]
destination=[]
weights=[]
global start_node
global node1
from sys import maxsize
INT_MAX = maxsize

#-------------------------------------------CLASS GRAPH---------------------------------------------
class Graph():
    def __init__(self,source,destination,weights,V,E):
        self.source=source
        self.destination=destination
        self.weights=weights
        self.V=V
        self.E=E
        self.src=0
    def Initialize(self,list_of_xaxis,list_of_yaxis,start_node,GraphMat,parent):
        self.list_of_xaxis=list_of_xaxis
        self.list_of_yaxis=list_of_yaxis
        self.start_node=start_node
        self.GraphMat=GraphMat
        self.parent=parent
    def Edges(self):
        root3 = Tk()
        j=0
        k=0
        View1 = Canvas(root3, width=1200, height=800,bg="#000000").grid(columnspan=15, rowspan=self.E,row=0)
        for i in range(self.E):
            str1=str(self.source[i])+"----->"+str(self.destination[i])+"  Weight:"+str(self.weights[i])
            if(k%20==0):
                j+=1
                k=0
            Label(root3, text=str1,font=("Raleway",8), bg="#000000", fg="white").grid(column=j, row=k,columnspan=1)
            k+=1
        root.mainloop()
    
#-------------------------------------------- XY PLOT -----------------------------------------------  
    def XYPlot(self):
        G = nx.Graph()
        for i in range(len(list_of_xaxis)):
            G.add_edges_from([(list_of_xaxis[i],list_of_yaxis[i])])
        plt.title("       XY PLOT      Number of Nodes =" + str (self.V))
        plt.plot(list_of_xaxis,list_of_yaxis)
        plt.show()
#-----------------------------------------UNDIRECTED GRAPH-------------------------------------------
    def UndirectedGraph(self):
        G = nx.Graph()
        # for i in range(num_of_nodes):
        #     G.add_node(i,pos=(round((float(list_of_xaxis[i])*10)),round((float(list_of_yaxis[i])*10))))
        for i in range(self.E):
            G.add_edges_from([(self.source[i],self.destination[i])], weight=self.weights[i])
        labels=nx.get_edge_attributes(G,'weight')
        # pos=nx.get_node_attributes(G,'pos')
        plt.title("       Undirected Graph      Number of Nodes =" + str (self.V))
        pos=nx.spring_layout(G)
        nx.draw_networkx_edge_labels(G,pos, edge_labels=labels,font_size=10,label_pos=0.5,font_weight="bold",font_color="#1d2d47")
        nx.draw(G,pos,with_labels=True,node_size=200,font_size=10,node_color="#808080",font_color="black",font_weight="bold")
        plt.show()
#-----------------------------------------DIRECTED GRAPH-------------------------------------------
    def DirectedGraph(self):
        G = nx.DiGraph()
        # for i in range(num_of_nodes):
        #     G.add_node(i,pos=(round((float(list_of_xaxis[i])*10)),round((float(list_of_yaxis[i])*10))))
        for i in range(self.E):
            G.add_edges_from([(self.source[i],self.destination[i])], weight=self.weights[i])
        labels=nx.get_edge_attributes(G,'weight')
        # pos=nx.get_node_attributes(G,'pos')
        pos=nx.spring_layout(G,k=15)
        plt.title("       Directed Graph      Number of Nodes =" + str (self.V))
        nx.draw_networkx_edge_labels(G,pos, edge_labels=labels,font_size=10,label_pos=0.5,font_weight="bold",font_color="#1d2d47")
        nx.draw(G,pos,with_labels=True,node_size=200,font_size=10,node_color="#808080",font_color="black",font_weight="bold")
        plt.show()

#-----------------------------------------Print GRAPH-------------------------------------------
    def PrintGraph(self,source,destination,weights,E,str1,str2):
        G = nx.DiGraph()
        # for i in range(num_of_nodes):
        #     G.add_node(i,pos=(round((float(list_of_xaxis[i])*10)),round((float(list_of_yaxis[i])*10))))
        for i in range(E):
            G.add_edges_from([(source[i],destination[i])], weight=weights[i])
        labels=nx.get_edge_attributes(G,'weight')
        # pos=nx.get_node_attributes(G,'pos')
        pos=nx.spring_layout(G,k=15)
        plt.title("  "+str1+"   "+str2+"  Number of Nodes =" + str(self.V))
        nx.draw_networkx_edge_labels(G,pos, edge_labels=labels,font_size=10,label_pos=0.5,font_weight="bold",font_color="#401414")
        nx.draw(G,pos,with_labels=True,node_size=200,font_size=10,node_color="#808080",font_color="black",font_weight="bold")
        plt.show()
#-----------------------------------------Prims Algorithm-------------------------------------------
    def isValidEdge(self,u, v, inMST):
        if u == v:
            return False
        if inMST[u] == False and inMST[v] == False:
            return False
        elif inMST[u] == True and inMST[v] == True:
            return False
        return True
 
    def Prims(self):

        dist = self.GraphMat
        # list(map(lambda p: list(map(lambda q: q, p)), self.GraphMat))
        # print(dist)
        INF = 999
        for p in range(self.V):
                for q in range(self.V):
                    if(dist[p][q]==0):
                        dist[p][q]= INT_MAX

        inMST = [False] * self.V
    
        # Include first vertex in MST
        inMST[0] = True
    
        # Keep adding edges while number of included
        # edges does not become V-1.
        edge_count = 0
        mincost = 0
        s=[]
        d=[]
        w=[]
        while edge_count < self.V - 1:
    
            # Find minimum weight valid edge.
            minn = INT_MAX
            a = -1
            b = -1
            for i in range(self.V):
                for j in range(self.V):
                    if dist[i][j] < minn:
                        if self.isValidEdge(i, j, inMST):
                            minn = dist[i][j]
                            a = i
                            b = j
            if a != -1 and b != -1:
                # print("Edge %d: (%d, %d) cost: %0.2f" %
                #     (edge_count, a, b, minn))
                s.append(a)
                d.append(b)
                w.append(minn)
                edge_count += 1
                mincost += minn
                inMST[b] = inMST[a] = True
        str1="Prims Graph"
        mincost=round(mincost,2)
        str2="Minimum cost = " + str(mincost)
        self.PrintGraph(s,d,w,edge_count,str1,str2)
        # print(s)
        # print(d)
        # print(w)
        # print("Minimum cost = %0.2f" % mincost)
#-----------------------------------------Kruskal's Algorithm'-------------------------------------------------

    # Find set of vertex i
    def findx(self,i):
        while parent[i] != i:
            i = parent[i]
        return i
    
    # Does union of i and j. It returns
    # false if i and j are already in same
    # set.
    def unionx(self,i, j):
        a = self.findx(i)
        b = self.findx(j)
        parent[a] = b
    
    # Finds MST using Kruskal's algorithm
    def Kruskal(self):
        dist = self.GraphMat
        # list(map(lambda p: list(map(lambda q: q, p)), self.GraphMat))
        # print(dist)
        for p in range(self.V):
                for q in range(self.V):
                    if(dist[p][q]==0):
                        dist[p][q]= INT_MAX
        mincost = 0 # Cost of min MST
    
        # Initialize sets of disjoint sets
        for i in range(self.V):
            parent[i] = i
    
        # Include minimum weight edges one by one
        edge_count = 0
        s1=[]
        d1=[]
        w1=[]
        while edge_count < self.V - 1:
            min = INF
            a = -1
            b = -1
            for i in range(self.V):
                for j in range(self.V):
                    if self.findx(i) != self.findx(j) and dist[i][j] < min:
                        min = dist[i][j]
                        a = i
                        b = j
            self.unionx(a, b)
            # print('Edge {}:({}, {}) cost:{}'.format(edge_count, a, b, min))
            s1.append(a)
            d1.append(b)
            w1.append(min)
            edge_count += 1
            mincost += min
        mincost=round(mincost,2)
        str1="Krushkal Graph"
        str2="Minimum cost = " + str(mincost)
        self.PrintGraph(s1,d1,w1,edge_count,str1,str2)
        # print("Minimum cost= %.02f"%(mincost))

#-----------------------------------------Floyd Warshall------------------------------------------------------

    def floyd(self):
        dist = self.GraphMat
        # print(GraphMat)
        # list(map(lambda p: list(map(lambda q: q, p)), self.GraphMat))
        # print(dist)
        INF =999
        for p in range(self.V):
                for q in range(self.V):
                    if(dist[p][q]==0):
                        dist[p][q]= INF
        for p in range(self.V):
                     dist[p][p]=0
        # Adding vertices individually
        # list(map(lambda p: list(map(lambda q: q, p)), dist))
        for r in range(self.V):
            for p in range(self.V):
                for q in range(self.V):
                    #print(dist[p][q]," ",dist[p][r]," ",dist[r][q])
                    dist[p][q] = min(dist[p][q], dist[p][r] + dist[r][q])
                   
        # for p in range(self.V):
        #     for q in range(self.V):
        #         if(dist[p][q] == INT_MAX):
        #             dist[p][q]=0
        #print(GraphMat)
        # for p in range(self.V):
        #         dist[p][p]=0
        edge_count = 0
        s2=[]
        d2=[]
        w2=[]       
        for p in range(self.V):
            for q in range(self.V):
                if(dist[p][q] != INF and dist[p][q] != 0):
                    s2.append(p)
                    d2.append(q)
                    w2.append(dist[p][q])
                    edge_count+=1
        str1="Floyd Warshal Graph"
        str2=""
        # print(s)
        # print(d)
        # print(w)
        # print(edge_count)
        self.PrintGraph(s2,d2,w2,edge_count,str1,str2)      
#-----------------------------------------Dijsktra Algorithm'-------------------------------------------------
     # A utility function to find the vertex with
    # minimum distance value, from the set of vertices
    # not yet included in shortest path tree
    def minDistance(self, dist, sptSet):
 
        # Initialize minimum distance for next node
        min = sys.maxsize
 
        # Search not nearest vertex not in the
        # shortest path tree
        for v in range(self.V):
            if dist[v] < min and sptSet[v] == False:
                min = dist[v]
                min_index = v
 
        return min_index
 
    # Function that implements Dijkstra's single source
    # shortest path algorithm for a graph represented
    # using adjacency matrix representation
    def Dijkstra(self):
        # root2.destroy()
        Dij = Tk()
        View1 = Canvas(Dij, width=500, height=100,bg="#000000").grid(columnspan=5, rowspan=1,row=0)
        Label(Dij, text="           Dijkstra Graph!",font=("Raleway",18), bg="#000000", fg="white").grid(column=0, row=0,columnspan=4)
        View2 = Canvas(Dij, width=500, height=25,bg="#808080").grid(columnspan=5, rowspan=1,row=2)
        View3 = Canvas(Dij, width=500, height=200,bg="#000000").grid(columnspan=5, rowspan=5,row=3,column=0)
        Label(Dij, text="  Please Enter Source Node",font=("Raleway",12), bg="#000000", fg="white").grid(column=0, row=4,columnspan=5)
        input=Entry(Dij,width=10)
        input.grid(row=5,column=0,columnspan=5)
        def Initialize():
            global st
            st=input.get()
            Dij.destroy()
        btn10 = Button(Dij, text="Submit", font=("Raleway",10), bg="#808080", fg="black",command=Initialize).grid(column=0, row=6,columnspan=5)
        Dij.mainloop() 

        src=int(st)
        dist = [sys.maxsize] * self.V
        dist[src] = 0
        sptSet = [False] * self.V
 
        for cout in range(self.V):
 
            # Pick the minimum distance vertex from
            # the set of vertices not yet processed.
            # u is always equal to src in first iteration
            u = self.minDistance(dist, sptSet)
 
            # Put the minimum distance vertex in the
            # shortest path tree
            sptSet[u] = True

            # Update dist value of the adjacent vertices
            # of the picked vertex only if the current
            # distance is greater than new distance and
            # the vertex in not in the shortest path tree
            for v in range(self.V):
                if self.GraphMat[u][v] > 0 and sptSet[v] == False and dist[v] > dist[u] + self.GraphMat[u][v]:
                    dist[v] = dist[u] + self.GraphMat[u][v]
        s3=[]
        d3=[]
        w3=[]
        for i in range(self.V-1):
            s3.append(src)
        for i in range(self.V):
            if(i==src):
                continue
            d3.append(i)
        for i in range(self.V):
            if(i==src):
                continue
            w3.append(dist[i])
        # print(s)
        # print(d)
        # print(w)
        str1="Dijkstra Graph"
        str2=""
        self.PrintGraph(s3,d3,w3,self.V-1,str1,str2)
        # print("Vertex tDistance from Source Dijkstra")
        # for node in range(self.V):
        #     print(node, "\t", dist[node])

#-----------------------------------------Bellman Ford Algorithm'-------------------------------------------------
    def BellmanFord(self):
        # root2.destroy()
        Dij = Tk()
        View1 = Canvas(Dij, width=500, height=100,bg="#000000").grid(columnspan=5, rowspan=1,row=0)
        Label(Dij, text="           Bellman Ford Graph!",font=("Raleway",18), bg="#000000", fg="white").grid(column=0, row=0,columnspan=4)
        View2 = Canvas(Dij, width=500, height=25,bg="#808080").grid(columnspan=5, rowspan=1,row=2)
        View3 = Canvas(Dij, width=500, height=200,bg="#000000").grid(columnspan=5, rowspan=5,row=3,column=0)
        Label(Dij, text="  Please Enter Source Node",font=("Raleway",12), bg="#000000", fg="white").grid(column=0, row=4,columnspan=5)
        input=Entry(Dij,width=10)
        input.grid(row=5,column=0,columnspan=5)
        def Initialize():
            global st
            st=input.get()
            Dij.destroy()
        btn10 = Button(Dij, text="Submit", font=("Raleway",10), bg="#808080", fg="black",command=Initialize).grid(column=0, row=6,columnspan=5)
        Dij.mainloop()     
        src=int(st)
        dist = self.GraphMat
        # list(map(lambda p: list(map(lambda q: q, p)), self.GraphMat))
        # print(dist)
        INF = 999
        for p in range(self.V):
                for q in range(self.V):
                    if(dist[p][q]==0):
                        dist[p][q]= INF

        for p in range(self.V):
                dist[p][p]=0

        # Initialize distance of all vertices as infinite.
        dis = [maxsize] * self.V
        # initialize distance of source as 0
        dis[src] = 0
    
        # Relax all edges |V| - 1 times. A simple
        # shortest path from src to any other
        # vertex can have at-most |V| - 1 edges
        for i in range(self.V - 1):
            for j in range(self.V):
                    for k in range(self.V):
                        x=j
                        y=k
                        if x!=y and dis[x]!=INF and dis[x] + dist[x][y] < dis[y]:
                            dis[y] = dis[x] + dist[x][y]
    
        # check for negative-weight cycles.
        # The above step guarantees shortest
        # distances if graph doesn't contain 
        # negative weight cycle. If we get a
        # shorter path, then there is a cycle.
        # for i in range(E):
        #     x = GraphMat[i][0]
        #     y = GraphMat[i][1]
        #     weight = GraphMat[i][2]
        #     if dis[x] != maxsize and dis[x] + \
        #                     weight < dis[y]:
        #         print("Graph contains negative weight cycle")
        s5=[]
        d5=[]
        w5=[]
        for i in range(self.V-1):
            s5.append(src)
        for i in range(self.V):
            if(i==src):
                continue
            d5.append(i)
        for i in range(self.V):
            if(i==src):
                continue
            w5.append(dis[i])
        # print(s)
        # print(d)
        # print(w)
        str1="Bellman Ford Graph"
        str2=""
        self.PrintGraph(s5,d5,w5,self.V-1,str1,str2)
        # print("Vertex Distance from Source Bellman")
        # for i in range(self.V):
        #     print("%d \t %0.2f" % (i, dis[i]))
#-----------------------------------------Clustering Coefficient------------------------------------------------
    def ClusteringCoeff(self):
        # print(UndirectedGraphMat)
        degree=[]
        neighbor_edges=[]
        neighbor=[]
        # print(neighbor_edges)
        for i in range (self.V):
            temp=0
            neighbor.clear()
            for j in range(self.V):
                if(self.GraphMat[i][j]!=0 or self.GraphMat[j][i]!=0):
                    temp+=1
                    neighbor.append(j)
            degree.append(temp)
            # print(neighbor)
            count=0
            for k in range(len(neighbor)-1):
                l=k+1
                dis=len(neighbor)
                while(l<dis):
                    if(self.GraphMat[neighbor[k]][neighbor[l]]!=0 or self.GraphMat[neighbor[l]][neighbor[k]]!=0):
                        count+=1
                    l+=1
            neighbor_edges.append(count)
            # print(neighbor_edges)
        # print(degree)
        # print(neighbor_edges)
        #-------------------USING CLUSTERING FORMULA-------------------------------
        CC=[]
        for i in range(self.V):
            t1=2*neighbor_edges[i]
            t2=degree[i]*(degree[i]-1)
            if(t2==0):
                continue
            temp=t1/t2
            temp=round(temp,3)
            CC.append(temp)
        root3 = Tk()
        j=0
        k=2
        View1 = Canvas(root3, width=500, height=500,bg="#000000").grid(columnspan=15, rowspan=20,row=0)
        Label(root3, text="Clustering Coeffients",font=("Raleway",15), bg="#000000", fg="white").grid(column=0, row=1,columnspan=15)
        for i in range(self.V):
            str1=str(i)+"----------->"+str(CC[i])
            if(k%20==0):
                j+=1
                k=2
            Label(root3, text=str1,font=("Raleway",8), bg="#000000", fg="white").grid(column=j, row=k,columnspan=1)
            k+=1
        root.mainloop()                   


#---------------------------------------End of class Graph-----------------------------------------------

#---------------------------------------Boruvkas Algorithm-----------------------------------------------

class Graph2:
    
    def __init__(self,vertices):
        self.V= vertices #No. of vertices
        self.graph = [] # default dictionary to store graph
    #-----------------------------------------Print GRAPH-------------------------------------------
    def PrintGraph(self,source,destination,weights,E,str1,str2):
        G = nx.DiGraph()
        # for i in range(num_of_nodes):
        #     G.add_node(i,pos=(round((float(list_of_xaxis[i])*10)),round((float(list_of_yaxis[i])*10))))
        for i in range(E):
            G.add_edges_from([(source[i],destination[i])], weight=weights[i])
        labels=nx.get_edge_attributes(G,'weight')
        # pos=nx.get_node_attributes(G,'pos')
        pos=nx.spring_layout(G,k=15)
        plt.title("  "+str1+"   "+str2+"  Number of Nodes =" + str(self.V))
        nx.draw_networkx_edge_labels(G,pos, edge_labels=labels,font_size=10,label_pos=0.5,font_weight="bold",font_color="#401414")
        nx.draw(G,pos,with_labels=True,node_size=200,font_size=10,node_color="#808080",font_color="black",font_weight="bold")
        plt.show() 
    #-----------------------------------------------------------------------------------------------------------------------          
   
    # function to add an edge to graph
    def addEdge(self,u,v,w):
        self.graph.append([u,v,w])
  
    # A utility function to find set of an element i
    # (uses path compression technique)
    def find(self, parent, i):
        if parent[i] == i:
            return i
        return self.find(parent, parent[i])
    # A function that does union of two sets of x and y
    # (uses union by rank)
    def union(self, parent, rank, x, y):
        xroot = self.find(parent, x)
        yroot = self.find(parent, y)
  
        # Attach smaller rank tree under root of high rank tree
        # (Union by Rank)
        if rank[xroot] < rank[yroot]:
            parent[xroot] = yroot
        elif rank[xroot] > rank[yroot]:
            parent[yroot] = xroot
        #If ranks are same, then make one as root and increment
        # its rank by one
        else :
            parent[yroot] = xroot
            rank[xroot] += 1
  
    # The main function to construct MST using Kruskal's algorithm
    def boruvkaMST(self):
        parent = []; rank = []; 
        # print(self.graph)
        s=[]
        d=[]
        wt=[]
        # An array to store index of the cheapest edge of
        # subset. It store [u,v,w] for each component
        cheapest =[]
  
        # Initially there are V different trees.
        # Finally there will be one tree that will be MST
        numTrees = self.V
        MSTweight = 0
  
        # Create V subsets with single elements
        for node in range(self.V):
            parent.append(node)
            rank.append(0)
            cheapest =[-1] * self.V
      
        # Keep combining components (or sets) until all
        # compnentes are not combined into single MST
  
        while numTrees > 1:
  
            # Traverse through all edges and update
               # cheapest of every component
            for i in range(len(self.graph)):
  
                # Find components (or sets) of two corners
                # of current edge
                u,v,w =  self.graph[i]
                set1 = self.find(parent, u)
                set2 = self.find(parent ,v)
  
                # If two corners of current edge belong to
                # same set, ignore current edge. Else check if 
                # current edge is closer to previous
                # cheapest edges of set1 and set2
                if set1 != set2:     
                      
                    if cheapest[set1] == -1 or cheapest[set1][2] > w :
                        cheapest[set1] = [u,v,w] 
  
                    if cheapest[set2] == -1 or cheapest[set2][2] > w :
                        cheapest[set2] = [u,v,w]
  
            # Consider the above picked cheapest edges and add them
            # to MST
            # print(s)
            # print(d)
            # print(w)         
            for node in range(self.V):
  
                #Check if cheapest for current set exists
                if cheapest[node] != -1:
                    u,v,w = cheapest[node]
                    set1 = self.find(parent, u)
                    set2 = self.find(parent ,v)
  
                    if set1 != set2 :
                        MSTweight += w
                        self.union(parent, rank, set1, set2)
                        s.append(u)
                        d.append(v)
                        wt.append(w)
                        # print ("Edge %d-%d with weight %0.2f included in MST" % (u,v,w))
                        numTrees = numTrees - 1
              
            #reset cheapest array
            cheapest =[-1] * self.V
  
        str1="Boruvka MST Graph"
        mincost=round(MSTweight,2)
        str2="Minimum cost = " + str(mincost)
        self.PrintGraph(s,d,wt,self.V-1,str1,str2)              
        # print ("Weight of MST is %f" % MSTweight)
        
#---------------------------------------End of class Graph2-----------------------------------------------
#------------------------------------------Node Initialize Functions-------------------------------------
def Init10():
    global node1
    node1=10
    root.destroy()
def Init20():
    global node1
    node1=20
    root.destroy()
def Init30():
    global node1
    node1=30
    root.destroy()
def Init40():
    global node1
    node1=40
    root.destroy()
def Init50():
    global node1
    node1=50
    root.destroy()
def Init60():
    global node1
    node1=60
    root.destroy()
def Init70():
    global node1
    node1=70
    root.destroy()
def Init80():
    global node1
    node1=80
    root.destroy()
def Init90():
    global node1
    node1=90
    root.destroy()
def Init100():
    global node1
    node1=100
    root.destroy()
#----------------------------------------Interface Window 1----------------------------------------------
global root
root = Tk()

View1 = Canvas(root, width=500, height=100,bg="#000000").grid(columnspan=5, rowspan=1,row=0)
Label(root, text="           Welcome the the World Of Graphs!",font=("Raleway",18), bg="#000000", fg="white").grid(column=0, row=0,columnspan=4)
View2 = Canvas(root, width=500, height=25,bg="#808080").grid(columnspan=5, rowspan=1,row=2)
View3 = Canvas(root, width=500, height=300,bg="#000000").grid(columnspan=5, rowspan=8,row=3,column=0)
Label(root, text="  Please Click an Input Button",font=("Raleway",12), bg="#000000", fg="white").grid(column=0, row=3,columnspan=5)
btn10 = Button(root, text="10 Nodes", font="Raleway", bg="#808080", fg="black",command=Init10).grid(column=1, row=4)
btn20 = Button(root, text="20 Nodes", font="Raleway", bg="#808080", fg="black",command=Init20).grid(column=3, row=4)
btn30 = Button(root, text="30 Nodes", font="Raleway", bg="#808080", fg="black",command=Init30).grid(column=1, row=5)
btn40 = Button(root, text="40 Nodes", font="Raleway", bg="#808080", fg="black",command=Init40).grid(column=3, row=5)
btn50 = Button(root, text="50 Nodes", font="Raleway", bg="#808080", fg="black",command=Init50).grid(column=1, row=6)
btn60 = Button(root, text="60 Nodes", font="Raleway", bg="#808080", fg="black",command=Init60).grid(column=3, row=6)
btn70 = Button(root, text="70 Nodes", font="Raleway", bg="#808080", fg="black",command=Init70).grid(column=1, row=7)
btn80 = Button(root, text="80 Nodes", font="Raleway", bg="#808080", fg="black",command=Init80).grid(column=3, row=7)
btn90 = Button(root, text="90 Nodes", font="Raleway", bg="#808080", fg="black",command=Init90).grid(column=1, row=8)
btn100 = Button(root, text="100 Nodes", font="Raleway", bg="#808080", fg="black",command=Init100).grid(column=3, row=8)

root.mainloop()
# #----------------------------------------End of Interface Window 1------------------------------------------

#------------------------------Reading all data from file and deleting irrelevent data-------------------------
with open("input" + str(node1) + ".txt", "r") as f:
    DataList = f.readlines()

DataList2 = [x.replace('\n', '') for x in DataList]
DataList2.remove('NETSIM')
while("" in DataList2) :
    DataList2.remove("")
num_of_nodes = int(DataList2[0]) 
DataList2.remove(DataList2[0])

# print(GraphList)
DataList2 = [i.split('\t') for i in DataList2]
# print(GraphList)
#-------------------------- --------Storing x and y cordinates-------------------------------------------
for i in range(num_of_nodes):
    del (DataList2[i][0])
    list_of_xaxis.append(DataList2[i][0])
    list_of_yaxis.append(DataList2[i][1])
count = 0
index = 0
#----------------------------------Deleting xy cordinates from list------------------------
while (count<num_of_nodes):
    del DataList2[index]
    count +=1

#-----------------------------------Removing '' from list----------------------
for x in range(len(DataList2)):                            
    for y in range(len(DataList2[x])):
        if (DataList2[x][y] == ''):
            del DataList2[x][y]

#-----------------------------------Reading Edges and weights from file-------------------
rows,columns=(num_of_nodes,num_of_nodes)
GraphMat=[[0 for i in range(columns)] for j in range(rows)]
# print(GraphMat)
edges=0
for x in range(len(DataList2)):  
    temp=int(DataList2[x][0])               
    y=0               
    while(y<(len(DataList2[x])-4)):
        # print(x," ",y)
        x_cor=temp
        y_cor=int(DataList2[x][y+1])
        w=float(float(DataList2[x][y+3])/10000000)
        # print(x_cor, " ",y_cor, " ",wheight )
        y+=4
        if(x_cor==y_cor):                       #Ignoring self link
            continue
        GraphMat[x_cor][y_cor]=w
        source.append(x_cor)
        destination.append(y_cor)
        weights.append(w)
        # print(GraphList[x_cor][y_cor])
        edges=edges+1
num_of_edges=edges
# print(GraphMat)
start_node=DataList2[num_of_nodes][0]
rows,columns=(num_of_nodes,0)
GraphList=[[0 for i in range(columns)] for j in range(rows)]
for i in range(num_of_edges):
    GraphList[source[i]].append(destination[i])
    GraphList[source[i]].append(weights[i])
parent=[]
for i in range(num_of_nodes):
    parent.append(i)
# print(parent)
# print(GraphList)
# for i in range(num_of_edges):
#     print(source[i], " ", destination[i], " ",weights[i])
# print(num_of_edges)
#-----------------------------------====Initializing Graph Object-----------------------------

g=Graph(source,destination,weights,num_of_nodes,num_of_edges)
g.Initialize(list_of_xaxis,list_of_yaxis,start_node,GraphMat,parent)
g2=Graph(source,destination,weights,num_of_nodes,num_of_edges)
g2.Initialize(list_of_xaxis,list_of_yaxis,start_node,GraphMat,parent)
g1=Graph2(num_of_nodes)
for i in range(num_of_nodes):
    for j in range(num_of_nodes):
        if GraphMat[i][j]!=0:
            g1.addEdge(i, j, GraphMat[i][j])
#----------------------------------------Interface Window 2----------------------------------------------
global root2
root2 = Tk()

View1 = Canvas(root2, width=600, height=100,bg="#000000").grid(columnspan=5, rowspan=1,row=0)
Label(root2, text="           Welcome the the World Of Graphs!",font=("Raleway",18), bg="#000000", fg="white").grid(column=0, row=0,columnspan=4)
View2 = Canvas(root2, width=600, height=25,bg="white").grid(columnspan=5, rowspan=2,row=1)
View3 = Canvas(root2, width=600, height=25,bg="white").grid(columnspan=5, rowspan=2,row=2)
btn1 = Button(root2, text="XY Plot", font=("Raleway",10), bg="black", fg="white",command=g.XYPlot).grid(column=0, row=2,columnspan=1)
btn1 = Button(root2, text="Directed Graph", font=("Raleway",10), bg="black", fg="white",command=g.DirectedGraph).grid(column=0, row=2,columnspan=3)
btn1 = Button(root2, text="Undirected Graph", font=("Raleway",10), bg="black", fg="white",command=g.UndirectedGraph).grid(column=1, row=2,columnspan=4)
btn1 = Button(root2, text="Edges", font=("Raleway",10), bg="black", fg="white",command=g.Edges).grid(column=3, row=2,columnspan=2)
View4 = Canvas(root2, width=600, height=25,bg="#808080").grid(columnspan=5, rowspan=2,row=3)
View5 = Canvas(root2, width=600, height=300,bg="#000000").grid(columnspan=5, rowspan=6,row=3,column=0)
Label(root2, text="Please select an Algorithm to Implement",font=("Raleway",12), bg="#000000", fg="white").grid(column=0, row=4,columnspan=5)
btn1 = Button(root2, text="Prims", font=("Raleway",10), bg="#808080", fg="black",command=g.Prims).grid(column=0, row=5,columnspan=2)
btn2 = Button(root2, text="Krushkal", font=("Raleway",10), bg="#808080", fg="black",command=g.Kruskal).grid(column=1, row=5,columnspan=2)
btn3 = Button(root2, text="Floyd Warshall", font=("Raleway",10), bg="#808080", fg="black",command=g2.floyd).grid(column=2, row=5,columnspan=2)
btn4 = Button(root2, text="Bellman Ford", font=("Raleway",10), bg="#808080", fg="black",command=g.BellmanFord).grid(column=0, row=6,columnspan=2)
btn5 = Button(root2, text="Dijkstra", font=("Raleway",10), bg="#808080", fg="black",command=g.Dijkstra).grid(column=1, row=6,columnspan=2)
btn6 = Button(root2, text="Boruvka's", font=("Raleway",10), bg="#808080", fg="black",command=g1.boruvkaMST).grid(column=2, row=6,columnspan=2)
btn7 = Button(root2, text="Clustering", font=("Raleway",10), bg="#808080", fg="black",command=g2.ClusteringCoeff).grid(column=3, row=6,columnspan=2)

root2.mainloop()
# #----------------------------------------End of Interface Window 2------------------------------------------



# g.XYPlot()
# g.UndirectedGraph()
# g1.boruvkaMST()
# g.DirectedGraph()
# g.Prims()
# g.Kruskal()
# g.floyd()
# g.BellmanFord(5)
# print("Enter Source Node: ")
# source=int(input())
# g.Dijkstra(5)




