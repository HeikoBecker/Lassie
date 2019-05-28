# Natural Language for Robots

- **[A Model for Verifiable Grounding and Execution of Complex Natural Language Instructions](http://ieeexplore.ieee.org/document/7759412/)**. Adrian Boteanu and others. IROS 2016. 
  - connects the work on grounding to verifiable execution: robot receives a request, performs grounding of expressions to physical entities and then it tries to verify the request. If it is verifiable, it increases its trust that the grounding process was done correctly.

- **[Efficient Grounding of Abstract Spatial Concepts for Natural Language Interaction with Robot Manipulators](http://www.roboticsproceedings.org/rss12/p37.html)**. Nicholas Roy and others. Robotics: Science and Systems. 2016.
  - deals with problem of grounding. Builds on previous work and introduces notions of cardinality and ordinality (e.g. tries to ground sentences like *take the first red cube in the second row*

- **[LTLMoP: Experimenting with language, Temporal Logic and robot control](http://ieeexplore.ieee.org/document/5650371/)**. C. Finucane, H. Kress-Gazit, G. Jing. IROS. 2010.
  - describes the tool that is based on *Translating structured english to robot controllers.* (down the list)

- **[Learning Environmental Knowledge from Task- Based Human-Robot Dialog](http://ieeexplore.ieee.org/document/6631186/)**. T. Kollar and others. ICRA. 2013.
  - checks its understanding through the dialog with human
  - can only understand fixed subset of actions and the commands can be made more complex

- **[Learning to Interpret Natural Language Commands through Human-Robot Dialog](http://www.ijcai.org/Abstract/15/273)**. J. Thomason. IJCAI. 2015.
  - based on a dialog with human
  - actions are of the structure *action-patient-recipien*
  - robot can learn new expressions for previously known objects, but can't go about learning more complex actions

- **[Provably correct reactive control from natural language](https://link.springer.com/article/10.1007%2Fs10514-014-9418-8)**. C. Lignos, V. Raman, C. Finucane, M.Marcus and H. Kress-Gazit. Autonomous Robots. 2015.
  - based on a list of previous work, does many things
  - using general NLP methods to get the syntactic and semantic structure of the utterance, VerbNet frames for meanings
  - using a fixed set of implemented behaviors
  - robot is able to respond to the question *What are you currently doing?*
  - very nice testing with natural incentives using video game  

- **[Understanding Natural Language Commands for Robotic Navigation and Mobile Manipulation](https://www.aaai.org/ocs/index.php/AAAI/AAAI11/paper/view/3623)**. S. Tellex and others. AAAI. 2011.
	- the problem of grounding the expressions to physical objects in robot's environment
	- they introduce a hierarchy (argument structure). in the previous work "beside the truck" could be learned, but wouldn't give any advantage when learning "beside the box". Now it is possible
	- structured of SDCs: relation, figure, landmark. For example, "Put the pallet on the truck"
  	SDC: f = none, r = "put", l1 = "the pallet", l2 = "on the truck"	
	SDC2: f = "the pallet"
	SDC3: r = "on" l = "the truck"
	SDC4 = f = "the truck" 

- **[Translating Structured English to Robot Controllers](http://www.tandfonline.com/doi/abs/10.1163/156855308X344864)**. H. Kress-Gazit. Advanced Robotics. 2008.
  - in order to make LTL specification easier this paper introduces *structured English* - a subset of English that resembles LTL
  - user can express complex command in it, but the knowledge of LTL and its logic is still necessary and there is no way to simplify it

-**[RoboFlow: A Flow-based Visual Programming Language for Mobile Manipulation Tasks](https://doi.org/10.1109/ICRA.2015.7139973)**. S. Alexandrova et al. ICRA. 2016.
	- a flow-based language is presented
	- the authors tried to hit the sweet spot between intuitiveness and expressibility
	- area of programming by users, same motivation as for lasre

# Semantic Parsers

- **[Improved Semantic Parsers For If-Then Statements](http://aclweb.org/anthology/P/P16/P16-1069.pdf)**. C. Quirk and I. Beltagy. ACL. 2016.
	- works on ifttt dataset an builds a model from translating very loose descriptions into executable representation
	- suggests a list of methods to improve basic model: paraphrasing and sythetic training, ensembles of multiple systems etc.

- **[Learning Executable Semantic Parsers for Natural Language Understanding](https://dl.acm.org/citation.cfm?doid=2866568)**. P. Liang. Communications of ACM. 2016.
  - describes all the parts of a semantic parser and explains few tehcniques available for building one

- **[Instructable Intelligent Personal Agent](https://www.aaai.org/ocs/index.php/AAAI/AAAI16/paper/view/12383)**. A. Azaria and others. AAAI. 2016.

- **[SQLizer: query synthesis from natural language](https://dl.acm.org/citation.cfm?doid=3133887)**. N. Yaghmazadeh and others. OOPSLA. 2017.


# Natural Language Programming

- **[Understanding Natural Language](https://ac.els-cdn.com/0010028572900023/1-s2.0-0010028572900023-main.pdf?_tid=5f84748e-17ae-11e8-8136-00000aacb362&acdnat=1519290013_fd17608d2125bfdfd484a61d960c2880)**. Terry Winograd. Cognitive Psychology. 1972.
  - a work that started the field, had an ambition of *understanding language*, assuming that the system has a detailed model of the discussed topic

- **[Language to Code: Learning Semantic Parsers for If-This-Then-That Recipes](http://aclweb.org/anthology/P/P15/P15-1085.pdf)**. C. Quirk and others. ACL. 2015.

- **[Naturalizing a Programming Language via Interactive Learning](http://aclweb.org/anthology/P17-1086)**. S. Wang and others. ACL. 2017.
  - introduces the concept of starting from a formal language and gradually naturalizing it
  - base for lasre
  

- **[Learning Language Games through Interaction](hhttps://arxiv.org/pdf/1606.02447.pdf)**. S. Wang and others. ACL. 2016. 

- **[Program Synthesis from Natural Language Using Recurrent Neural Networks](http://victorialin.net/pubs/tellina_tr180201.pdf)**. V. Lin and others. UW technical report. 2017.
  - going from problem formulation to bash one-liners
  - they use RNN to learn the structure of the program and then k-NN for matching entities into slots
  


