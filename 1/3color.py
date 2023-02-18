"""
HOW TO USE THIS FILE
install z3 (and the z3 python bindings), networkx, matplotlib.

run this file. it will print whether G and H are colorable and show
a 3-coloring of H.

you may also import this file and use color3 as an oracle to
check whether arbitrary networkx graphs are colorable.

if you pass a matplotlib axis to color3 as the draw keyword argument,
it will draw the coloring on the axis if it succeeds.

if you pass a filename to color3 as the save keyword argument,
it will save the smt2 constraints to that file.
NOTE: it will not save a (check-sat), you have to write that yourself.
"""


import networkx as nx
import z3
import matplotlib.pyplot as plt

def color3(graph, draw=None, save=None):
	"""
	given an arbitrary networkx graph, attempt to 3color it.
	if it is not possible to color it, then this function returns False.
	otherwise, this function returns True.
	"""
	# associate nodes with integers.
	nodes = {x:i for i,x in enumerate(graph.nodes)}
	
	# rgb props for each 
	props = [z3.Bools(f"{i}_#ff0000 {i}_#00ff00 {i}_#0000ff") for i in graph.nodes]

	s = z3.Solver()

	# nodes must be exactly one of three colors.
	for (r,g,b) in props:
		s.add(z3.Xor(z3.Xor(r,g),b))
	
	# nodes cannot be the same color as their neighbors.
	for (w,v) in graph.edges:
		for (p1,p2) in zip(props[nodes[w]], props[nodes[v]]):
			s.add(z3.Not(z3.And(p1,p2)))
	
	if (save is not None):
		with open(save,"w") as f:
			f.write(s.sexpr())


	if (s.check() == z3.unsat):
		# no 3-coloring exists!
		return False

	model = s.model()

	if (draw is not None):
		nx.draw_networkx(graph,ax=draw,node_color=[
			str(max(props[nodes[e]],key=lambda x: z3.is_true(model[x]) )).split("_")[1] for e in graph.nodes
		])

	
	return True


# simple tests
assert(color3(nx.complete_graph(4))==False)
assert(color3(nx.complete_graph(3))==True)


if __name__=="__main__":
	G = nx.Graph()
	G.add_edges_from([(0,1),(1,3),(3,2),(2,0),(0,3),(1,2)])

	H = nx.Graph()
	H.add_edges_from([(0,2),(2,3),(3,1),(1,0),(1,2),(2,4),(4,1)])

	print("G is 3colorable:",color3(G))

	print("H is 3colorable:",color3(H))

	# I know that H is colorable so let's draw it.
	color3(H,plt.gca())
	plt.title("H 3-coloring")
	plt.show()
