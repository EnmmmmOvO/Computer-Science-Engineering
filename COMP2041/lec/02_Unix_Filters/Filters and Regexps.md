# Filters and Regexps

This file contains examples of the use of the most common Unix filter programs (`grep`, `wc`, `head`, etc.) It also contains solutions to the exercises discussed in lectures.

1. Consider a a file [course_codes.tsv](/course_codes.tsv) containing UNSW course codes and names.

   ```
   ls -l course_codes.tsv
   -rw-r--r-- 1 cs2041 cs2041 907421 May 29 10:11 course_codes.tsv
   ```

   ```
   wc course_codes.tsv
    27383 119534 907421 course_codes.tsv
   ```

   ```
   head course_codes.tsv
   ACCT1501	Accounting & Financial Mgt 1A
   ACCT1511	Accounting & Financial Mgt 1B
   ACCT2101	Industry Placement 1
   ACCT2507	Intro to Accounting Research
   ACCT2511	Financial Acct Fundamentals
   ACCT2522	Management Acc for Decision
   ACCT2532	Management Accounting (Hons)
   ACCT2542	Corporate Financial Reporting
   ACCT2552	Corporate Financial Rep (Hons)
   ACCT2672	Accounting analytics
   ```

   It looks like the code is separated from the title by a number of spaces. We can check this via `cat -A`:

   ```
   head -5 course_codes.tsv | cat -A
   ACCT1501^IAccounting & Financial Mgt 1A$
   ACCT1511^IAccounting & Financial Mgt 1B$
   ACCT2101^IIndustry Placement 1$
   ACCT2507^IIntro to Accounting Research$
   ACCT2511^IFinancial Acct Fundamentals$
   ```

   This shows us that our initial guess was wrong, and there's actually a tab character between the course code and title (shown as `^I` by `cat -A`). Also, the location of the end-of-line marker (`$`) indicates that there are no trailing spaces or tabs.

   If we need to know what COMP courses there are:

   ```
   grep -E -c COMP course_codes.tsv
   251
   ```

   ```
   grep -E COMP course_codes.tsv
   COMP0001	Quality Management
   COMP0011	Fundamentals of Computing
   COMP1000	Web, Spreadsheets & Databases
   COMP1001	Introduction to Computing
   COMP1010	The Art of Computing
   COMP1011	Computing 1A
   COMP1021	Computing 1B
   COMP1081	Harnessing the Power of IT
   COMP1091	Solving Problems with Software
   COMP1400	Programming for Designers
   COMP1511	Programming Fundamentals
   COMP1521	Computer Systems Fundamentals
   COMP1531	Software Eng Fundamentals
   COMP1711	Higher Computing 1A
   COMP1721	Higher Computing 1B
   COMP1811	Computing 1 (Procedural)
   COMP1821	Computing 2
   COMP1911	Computing 1A
   COMP1917	Computing 1
   COMP1921	Computing 1B
   COMP1927	Computing 2
   COMP2011	Data Organisation
   COMP2021	Digital System Structures
   COMP2031	Concurrent Computing
   COMP2041	Software Construction
   COMP2091	Computing 2
   COMP2110	Software System Specification
   COMP2111	System Modelling and Design
   COMP2121	Microprocessors & Interfacing
   COMP2411	Logic and Logic Programming
   COMP2511	O-O Design & Programming
   COMP2521	Data Structures and Algorithms
   COMP2711	Higher Data Organisation
   COMP2811	Computing B
   COMP2911	Eng. Design in Computing
   COMP2920	Professional Issues and Ethics
   COMP3111	Software Engineering
   COMP3120	Introduction to Algorithms
   COMP3121	Algorithms & Programming Tech
   COMP3131	Programming Languages & Compil
   COMP3141	Software Sys Des&Implementat'n
   COMP3151	Foundations of Concurrency
   COMP3152	Comparative Concurrency Semant
   COMP3153	Algorithmic Verification
   COMP3161	Concepts of Programming Lang.
   COMP3171	Object-Oriented Programming
   COMP3211	Computer Architecture
   COMP3221	Microprocessors & Embedded Sys
   COMP3222	Digital Circuits and Systems
   COMP3231	Operating Systems
   COMP3241	Real Time Systems
   COMP3311	Database Systems
   COMP3331	Computer Networks&Applications
   COMP3411	Artificial Intelligence
   COMP3421	Computer Graphics
   COMP3431	Robotic Software Architecture
   COMP3441	Security Engineering
   COMP3511	Human Computer Interaction
   COMP3601	Design Project A
   COMP3710	Software Project Management
   COMP3711	Software Project Management
   COMP3720	Total Quality Management
   COMP3821	Ext Algorithms&Prog Techniques
   COMP3891	Ext Operating Systems
   COMP3900	Computer Science Project
   COMP3901	Special Project A
   COMP3902	Special Project B
   COMP3931	Ext Computer Networks & App
   COMP4001	Object-Oriented Software Dev
   COMP4002	Logic Synthesis & Verification
   COMP4003	Industrial Software Developmen
   COMP4011	Web Applications Engineering
   COMP4012	Occasional Elec S2 - Comp.Eng.
   COMP4022	Theory of Neural Nets
   COMP4111	Distributed Object Sys & Tech
   COMP4121	Advanced Algorithms
   COMP4128	Programming Challenges
   COMP4131	Programming Language Semantics
   COMP4132	Adv. Functional Programming
   COMP4133	Advanced Compiler Construction
   COMP4141	Theory of Computation
   COMP4151	Algorithmic Verification
   COMP4161	Advanced Verification
   COMP4181	Language-based Software Safety
   COMP4211	Adv Architectures & Algorithms
   COMP4215	Vlsi Systems Architecture and
   COMP4216	Distributed Operating Systems
   COMP4314	Next Generation Database Systs
   COMP4317	XML and Databases
   COMP4335	Wireless Mesh&Sensor Networks
   COMP4336	Mobile Data Networking
   COMP4337	Securing Fixed & Wireless Netw
   COMP4411	Experimental Robotics
   COMP4412	Introduction to Modal Logic
   COMP4415	First-order Logic
   COMP4416	Intelligent Agents
   COMP4418	Knowledge Representation
   COMP4431	Game Design Workshop
   COMP4442	Advanced Computer Security
   COMP4444	Neural Networks
   COMP4511	User Interface Design & Constr
   COMP4601	Design Project B
   COMP4903	Industrial Training (B.E.)
   COMP4904	Industrial Training 1
   COMP4905	Industrial Training 2
   COMP4906	Industrial Training 3
   COMP4910	Thesis Part A
   COMP4911	Thesis Part B
   COMP4913	Computer Science 4 Honours P/T
   COMP4914	Computer Science 4 Honours F/T
   COMP4920	Professional Issues and Ethics
   COMP4930	Thesis Part A
   COMP4931	Thesis Part B
   COMP4941	Thesis Part B
   COMP4951	Research Thesis A
   COMP4952	Research Thesis B
   COMP4953	Research Thesis C
   COMP4961	Computer Science Thesis A
   COMP4962	Computer Science Thesis B
   COMP4963	Computer Science Thesis C
   COMP6080	Web Front-End Programming
   COMP6324	IoT Services Engineering
   COMP6441	Security Engineering
   COMP6443	Web Application Security
   COMP6445	Digital Forensics
   COMP6447	Security Assessment
   COMP6448	Security Masterclass
   COMP6451	Cryptocurrency and DLT
   COMP6452	Blockchain App Architecture
   COMP6714	Info Retrieval and Web Search
   COMP6721	(In-)Formal Methods
   COMP6731	Combinatorial Data Processing
   COMP6733	Internet of Things
   COMP6741	Algorithms for Intractable Pbs
   COMP6752	Modelling Concurrent Systems
   COMP6771	Advanced C++ Programming
   COMP6841	Extended Security Engineering
   COMP6843	Extended WebApp Security
   COMP6845	Extended Digital Forensics
   COMP6991	Modern Prog Problems with Rust
   COMP8524	Postgraduate Elective 24 UOC
   COMP9000	Special Program
   COMP9001	E-Commerce Technologies
   COMP9002	XML and Databases
   COMP9008	Software Engineering
   COMP9009	Adv Topics in Software Eng
   COMP9011	Literacy and Programming
   COMP9012	Software Engineering and Tools
   COMP9013	Data Bases and Expert Systems
   COMP9014	Comp Organizat'n & Interfacing
   COMP9015	Issues in Computing
   COMP9018	Advanced Graphics
   COMP9020	Foundations of Comp. Science
   COMP9021	Principles of Programming
   COMP9022	Digital Systems Structures
   COMP9023	Functional Programming
   COMP9024	Data Structures & Algorithms
   COMP9031	Internet Programming
   COMP9032	Microprocessors & Interfacing
   COMP9041	Software Construction
   COMP9044	Software Construction
   COMP9081	Harnessing the Power of IT
   COMP9101	Design &Analysis of Algorithms
   COMP9102	Programming Lang & Compilers
   COMP9103	Algorithms & Comp. Complexity
   COMP9114	Formal Specification
   COMP9115	Prog Languages: Fund. Concepts
   COMP9116	S'ware Dev: B-Meth & B-Toolkit
   COMP9117	Software Architecture
   COMP9151	Foundations of Concurrency
   COMP9152	Comparative Concurrency Semant
   COMP9153	Algorithmic Verification
   COMP9154	Foundations of Concurrency
   COMP9161	Concepts of Programming Lang.
   COMP9164	Concepts of Programming Lang.
   COMP9171	Object-Oriented Programming
   COMP9181	Language-based Software Safety
   COMP9201	Operating Systems
   COMP9211	Computer Architecture
   COMP9214	Computer Org. & Architecture
   COMP9215	Vlsi System Design
   COMP9216	Parallel &Distributed Comp Sys
   COMP9221	Microprocessors & Embedded Sys
   COMP9222	Digital Circuits and Systems
   COMP9231	Integrated Digital Systems
   COMP9241	Supercomputing Techniques
   COMP9242	Advanced Operating Systems
   COMP9243	Distributed Systems
   COMP9244	Software View of Proc Architec
   COMP9245	Real-Time Systems
   COMP9283	Ext Operating Systems
   COMP9301	Cyber Security Project
   COMP9302	Cyber Security Project B
   COMP9311	Database Systems
   COMP9312	Data Analytics for Graphs
   COMP9313	Big Data Management
   COMP9314	Next Generation Database Systs
   COMP9315	Database Systems Implementat'n
   COMP9316	eCommerce Implementation
   COMP9317	XML and Databases
   COMP9318	Data Warehousing & Data Mining
   COMP9319	Web Data Compression & Search
   COMP9321	Data Services Engineering
   COMP9322	Software Service Design & Eng
   COMP9323	e-Enterprise Project
   COMP9331	Computer Networks&Applications
   COMP9332	Network Routing and Switching
   COMP9333	Advanced Computer Networks
   COMP9334	Systems Capacity Planning
   COMP9335	Wireless Mesh&Sensor Networks
   COMP9336	Mobile Data Networking
   COMP9337	Securing Fixed & Wireless Netw
   COMP9414	Artificial Intelligence
   COMP9415	Computer Graphics
   COMP9416	Knowledge Based Systems
   COMP9417	Machine Learning & Data Mining
   COMP9418	Advanced Machine Learning
   COMP9431	Robotic Software Architecture
   COMP9434	Robotic Software Architecture
   COMP9441	Security Engineering
   COMP9444	Neural Networks, Deep Learning
   COMP9447	Security Engineering Workshop
   COMP9491	Applied AI
   COMP9511	Human Computer Interaction
   COMP9514	Advanced Decision Theory
   COMP9515	Pattern Classification
   COMP9517	Computer Vision
   COMP9518	Pattern Recognition
   COMP9519	Multimedia Systems
   COMP9596	Research Project
   COMP9614	Linguistics
   COMP9701	Computer Graphics Using a Gui
   COMP9727	Recommender Systems
   COMP9790	Principles of GNSS Positioning
   COMP9791	Modern Navigation &Positioning
   COMP9801	Ext Design&Analysis of Algo
   COMP9814	Ext Artificial Intelligence
   COMP9833	Ext Computer Networks & Appl
   COMP9844	Ext Neural Networks
   COMP9900	Info Tech Project
   COMP9901	P/T Res. Thesis Comp Sci & Eng
   COMP9902	Res. Thesis Comp Sci & Eng F/T
   COMP9910	Mgt&Com Skills-CompSci&Eng Res
   COMP9912	Project (24 UOC)
   COMP9918	Project Report (90Cr)
   COMP9921	Personal Software Process for
   COMP9930	Readings in Comp Sci and Eng
   COMP9945	Research Project
   COMP9991	Research Project A
   COMP9992	Research Project B
   COMP9993	Research Project C
   ```

   Either of the two commands below tell us which courses have "comp" in their name or code (in upper or lower case).

   ```
   tr A-Z a-z <course_codes.tsv | grep -E comp
   aciv2503	eng computational meth 1a
   aciv2504	eng computational meth 1b
   aciv2518	eng computational methods 1
   aciv3503	eng computational methods 2a
   aciv3504	eng computational methods 2b
   aciv3516	eng computational methods 2
   acma2102	eng computational methods 1
   acma3102	eng computational methods 2
   acma4021	computer tools for eng mgt
   acsc1100	intro to computer science
   acsc1401	computer tools for engineers
   acsc1501	computer tools for engineers
   acsc1502	computer prog for engineers
   acsc1600	computer science 1
   acsc1800	computer science 1e
   acsc2004	comparative prog languages
   acsc2009	computer speech processing
   acsc2013	human computer interaction
   acsc2015	interactive computer graphics
   acsc2018	comp tools for decision making
   acsc2101	computer science core 2a
   acsc2102	computer science core 2b
   acsc2104	computer systems architecture
   acsc2106	computer languages & algorithm
   acsc2107	computer languages b
   acsc2109	computer technology
   acsc2405	computer architecture 2ee
   acsc2601	computer science 2a
   acsc2602	computer science 2b
   acsc2800	computer science 2e
   acsc2801	computer science 2ce
   acsc2802	computer science 2ee
   acsc2803	computer science 2ae
   acsc2804	computer science 2me
   acsc3003	computer project
   acsc3029	computing project 3
   acsc3030	cryptography & comp security 3
   acsc3034	human computer interaction 3
   acsc3102	human computer interaction
   acsc3601	computer science 3a
   acsc3603	computer science 3c
   acsc4191	computer science 4 (hons) f/t
   acsc4501	cryptog & computer security e
   acsc4502	computer speech e
   acsc4690	computer science 4 (hon) f/t
   acsc4691	computer science 4 (hon) p/t
   acsc7304	computer graphics
   acsc7306	computer speech processing
   acsc7316	it spec top 1: comput analysis
   acsc7336	computer security
   acsc7362	distributed computing
   acsc8201	intro to computer and info sys
   acsc8208	comp security & cryptography
   acsc8211	computer graphics
   acsc8218	computer speech processing
   acsc8226	evolutionary computation
   acsc8245	comp security & cryptography
   acsc8248	computer graphics
   acsc8256	comp speech processing
   acsc9000	computer science research f/t
   acsc9001	computer science research p/t
   aele2007	computer design
   aele2505	computer design
   aele2508	microcomputer interfacing
   aele3015	computer design
   aele3021	microcomputer interfacing 1
   aele3031	microcomputer interfacing
   aele3509	microcomputer interfacing
   aele4005	microcomputer interfacing a
   aele4072	computer control theory
   aele4511	computer control theory
   amat3026	complex analysis 3
   amat3107	complex variables
   amat3115	scientific computation
   amat3401	complex analysis 3e
   amat3503	complex variables e
   amec3023	composites and adhesives
   amec3512	pumps, turbines & compressors
   amec4005	composite mechanics
   amec4019	eng app of comp fluid dynamics
   amec4046	composite mechanics
   ance8001	computational mathematics
   ance8002	supercomputing techniques
   ance8103	fundamental applied computat'n
   ance8105	computational techniques
   ance9105	comp techniques fluid dynamics
   aphy3028	computational physics
   aphy3041	computational physics
   aphy3113	computational physics
   aphy3120	computers & electronics in phy
   aphy4003	microcomp. appl. in adv. mats.
   apol2617	intro to comparative politics
   apol3621	intro to comparative politics
   arch1391	digital computation studio
   arch5200	computer graphics programming
   arch5201	computer applications 1
   arch5202	computer applications 2
   arch5203	computer applications 3
   arch5205	theory of arch computing
   arch5220	computer graphics programming
   arch5221	computer graphics programming
   arch5222	computer applications 1
   arch5223	computer applications 2
   arch5940	theory of arch computing 1
   arch5941	theory of arch computing 2
   arch5942	arch computing seminar
   arch5943	theory of arch computing
   arch6201	architectural computing 1
   arch6205	architectural computing 2
   arch6214	architectural computing 2
   arch7204	design computing theory
   arch7205	computer graphics programming
   arch7221	computer modelling & rendering
   arts2301	computers, brains & minds
   atax0002	computer information systems
   atax0053	acct for complex struct & inst
   atax0324	gst: complex issues & planning
   atax0341	comparative tax systems
   atax0424	gst: complex issues & planning
   atax0441	comparative tax systems
   atax0641	comparative tax systems
   atax0903	legal comp database research
   atax0904	computer based acc spreadsheet
   atax0907	computer database
   aust2002	aboriginal stud: global comp 1
   aust2003	aboriginal stud: global comp 2
   aven1500	computing for aviation
   beil0003	be annual design competition
   beil0004	design competitions and bids
   benv1141	computers and information tech
   benv1242	computer-aided design
   benv2405	computer graphics programming
   benv2406	design and computation
   benv7503	geocomputation
   binf3020	computational bioinformatics
   binf9020	computational bioinformatics
   biom5912	comp thesis b&c
   biom5920	thesis part a (comp)
   biom5921	thesis part b (comp)
   biom9332	biocompatibility
   biom9334	comprehensive biomaterials sci
   biom9501	computing for biomedical eng
   biom9601	biomed applic.of microcomp 1
   biom9602	biomed applic.of microcomp 2
   bios3021	comparative animal physiology
   bldg2281	introduction to computing
   bldg3282	computer apps in building
   bldg5103	computers in management
   bldg6155	computers in construction mgmt
   ceic5310	comp studies in process ind
   ceic5335	adv comp methods process ind
   ceic6711	complex fluids
   ceic8310	computing studies proc ind
   chem3031	inorg chem:trans metals & comp
   chem3640	computers in chemistry
   civl1015	computing
   civl1106	computing & graphics
   civl3015	engineering computations
   civl3106	engineering computations
   civl9820	computational structural mech
   cmed9517	adv biostatistic & stat comp
   cmed9520	intro stat comp & stats in epi
   code1110	computational design theory 1
   code1150	computational design i
   code1210	computational design theory 2
   code1231	urban computing
   code1240	computational design 1
   code2110	computational design theory 3
   code2121	advanced computational design
   code2132	computational design 3 (urban)
   cofa1531	studio research -m'media comp1
   cofa1533	studio research -m'media comp3
   cofa2078	studio research basic comp
   cofa2080	std research composition&des
   cofa2680	multi-media computing unit 1
   cofa2681	multi-media computing unit 2
   cofa2682	multi-media computing unit 3
   cofa2683	multi-media computing unit 4
   cofa2684	multi-media computing unit 5
   cofa3680	m'media computing unit 1(elec)
   cofa3681	multimedia computing elective1
   cofa3682	multimedia computing elective2
   cofa3810	introduction to computing
   cofa3811	multimedia computing workshop
   cofa3835	composition & design workshop
   cofa3840	advanced multi-media computing
   cofa4036	the computer&the art educator
   cofa5106	design & comp: an introduction
   cofa5116	design and computers 1
   cofa5130	typography and composition
   cofa5208	design & computers:2d & 3d cad
   cofa5216	design and computers 1
   cofa5240	design and computers 2 cad
   cofa5241	design & computers 2 graphics
   cofa5308	design and timebased computer
   cofa5315	design and computers 2
   cofa5338	design and computers 3 - cad
   cofa5339	design&computers 3 - graphics
   cofa5434	design and computers 4
   cofa6315	design and computers s2 only
   cofa7006	applied arts wshop 2-comp tech
   cofa7051	computer technology 1
   cofa7052	computer technology 2
   cofa8670	intro to multimedia computing
   cofa9058	mae elective(design&computers)
   comd1000	intro to comparative develop't
   comm8004	becoming a complete scholar
   comp0001	quality management
   comp0011	fundamentals of computing
   comp1000	web, spreadsheets & databases
   comp1001	introduction to computing
   comp1010	the art of computing
   comp1011	computing 1a
   comp1021	computing 1b
   comp1081	harnessing the power of it
   comp1091	solving problems with software
   comp1400	programming for designers
   comp1511	programming fundamentals
   comp1521	computer systems fundamentals
   comp1531	software eng fundamentals
   comp1711	higher computing 1a
   comp1721	higher computing 1b
   comp1811	computing 1 (procedural)
   comp1821	computing 2
   comp1911	computing 1a
   comp1917	computing 1
   comp1921	computing 1b
   comp1927	computing 2
   comp2011	data organisation
   comp2021	digital system structures
   comp2031	concurrent computing
   comp2041	software construction
   comp2091	computing 2
   comp2110	software system specification
   comp2111	system modelling and design
   comp2121	microprocessors & interfacing
   comp2411	logic and logic programming
   comp2511	o-o design & programming
   comp2521	data structures and algorithms
   comp2711	higher data organisation
   comp2811	computing b
   comp2911	eng. design in computing
   comp2920	professional issues and ethics
   comp3111	software engineering
   comp3120	introduction to algorithms
   comp3121	algorithms & programming tech
   comp3131	programming languages & compil
   comp3141	software sys des&implementat'n
   comp3151	foundations of concurrency
   comp3152	comparative concurrency semant
   comp3153	algorithmic verification
   comp3161	concepts of programming lang.
   comp3171	object-oriented programming
   comp3211	computer architecture
   comp3221	microprocessors & embedded sys
   comp3222	digital circuits and systems
   comp3231	operating systems
   comp3241	real time systems
   comp3311	database systems
   comp3331	computer networks&applications
   comp3411	artificial intelligence
   comp3421	computer graphics
   comp3431	robotic software architecture
   comp3441	security engineering
   comp3511	human computer interaction
   comp3601	design project a
   comp3710	software project management
   comp3711	software project management
   comp3720	total quality management
   comp3821	ext algorithms&prog techniques
   comp3891	ext operating systems
   comp3900	computer science project
   comp3901	special project a
   comp3902	special project b
   comp3931	ext computer networks & app
   comp4001	object-oriented software dev
   comp4002	logic synthesis & verification
   comp4003	industrial software developmen
   comp4011	web applications engineering
   comp4012	occasional elec s2 - comp.eng.
   comp4022	theory of neural nets
   comp4111	distributed object sys & tech
   comp4121	advanced algorithms
   comp4128	programming challenges
   comp4131	programming language semantics
   comp4132	adv. functional programming
   comp4133	advanced compiler construction
   comp4141	theory of computation
   comp4151	algorithmic verification
   comp4161	advanced verification
   comp4181	language-based software safety
   comp4211	adv architectures & algorithms
   comp4215	vlsi systems architecture and
   comp4216	distributed operating systems
   comp4314	next generation database systs
   comp4317	xml and databases
   comp4335	wireless mesh&sensor networks
   comp4336	mobile data networking
   comp4337	securing fixed & wireless netw
   comp4411	experimental robotics
   comp4412	introduction to modal logic
   comp4415	first-order logic
   comp4416	intelligent agents
   comp4418	knowledge representation
   comp4431	game design workshop
   comp4442	advanced computer security
   comp4444	neural networks
   comp4511	user interface design & constr
   comp4601	design project b
   comp4903	industrial training (b.e.)
   comp4904	industrial training 1
   comp4905	industrial training 2
   comp4906	industrial training 3
   comp4910	thesis part a
   comp4911	thesis part b
   comp4913	computer science 4 honours p/t
   comp4914	computer science 4 honours f/t
   comp4920	professional issues and ethics
   comp4930	thesis part a
   comp4931	thesis part b
   comp4941	thesis part b
   comp4951	research thesis a
   comp4952	research thesis b
   comp4953	research thesis c
   comp4961	computer science thesis a
   comp4962	computer science thesis b
   comp4963	computer science thesis c
   comp6080	web front-end programming
   comp6324	iot services engineering
   comp6441	security engineering
   comp6443	web application security
   comp6445	digital forensics
   comp6447	security assessment
   comp6448	security masterclass
   comp6451	cryptocurrency and dlt
   comp6452	blockchain app architecture
   comp6714	info retrieval and web search
   comp6721	(in-)formal methods
   comp6731	combinatorial data processing
   comp6733	internet of things
   comp6741	algorithms for intractable pbs
   comp6752	modelling concurrent systems
   comp6771	advanced c++ programming
   comp6841	extended security engineering
   comp6843	extended webapp security
   comp6845	extended digital forensics
   comp6991	modern prog problems with rust
   comp8524	postgraduate elective 24 uoc
   comp9000	special program
   comp9001	e-commerce technologies
   comp9002	xml and databases
   comp9008	software engineering
   comp9009	adv topics in software eng
   comp9011	literacy and programming
   comp9012	software engineering and tools
   comp9013	data bases and expert systems
   comp9014	comp organizat'n & interfacing
   comp9015	issues in computing
   comp9018	advanced graphics
   comp9020	foundations of comp. science
   comp9021	principles of programming
   comp9022	digital systems structures
   comp9023	functional programming
   comp9024	data structures & algorithms
   comp9031	internet programming
   comp9032	microprocessors & interfacing
   comp9041	software construction
   comp9044	software construction
   comp9081	harnessing the power of it
   comp9101	design &analysis of algorithms
   comp9102	programming lang & compilers
   comp9103	algorithms & comp. complexity
   comp9114	formal specification
   comp9115	prog languages: fund. concepts
   comp9116	s'ware dev: b-meth & b-toolkit
   comp9117	software architecture
   comp9151	foundations of concurrency
   comp9152	comparative concurrency semant
   comp9153	algorithmic verification
   comp9154	foundations of concurrency
   comp9161	concepts of programming lang.
   comp9164	concepts of programming lang.
   comp9171	object-oriented programming
   comp9181	language-based software safety
   comp9201	operating systems
   comp9211	computer architecture
   comp9214	computer org. & architecture
   comp9215	vlsi system design
   comp9216	parallel &distributed comp sys
   comp9221	microprocessors & embedded sys
   comp9222	digital circuits and systems
   comp9231	integrated digital systems
   comp9241	supercomputing techniques
   comp9242	advanced operating systems
   comp9243	distributed systems
   comp9244	software view of proc architec
   comp9245	real-time systems
   comp9283	ext operating systems
   comp9301	cyber security project
   comp9302	cyber security project b
   comp9311	database systems
   comp9312	data analytics for graphs
   comp9313	big data management
   comp9314	next generation database systs
   comp9315	database systems implementat'n
   comp9316	ecommerce implementation
   comp9317	xml and databases
   comp9318	data warehousing & data mining
   comp9319	web data compression & search
   comp9321	data services engineering
   comp9322	software service design & eng
   comp9323	e-enterprise project
   comp9331	computer networks&applications
   comp9332	network routing and switching
   comp9333	advanced computer networks
   comp9334	systems capacity planning
   comp9335	wireless mesh&sensor networks
   comp9336	mobile data networking
   comp9337	securing fixed & wireless netw
   comp9414	artificial intelligence
   comp9415	computer graphics
   comp9416	knowledge based systems
   comp9417	machine learning & data mining
   comp9418	advanced machine learning
   comp9431	robotic software architecture
   comp9434	robotic software architecture
   comp9441	security engineering
   comp9444	neural networks, deep learning
   comp9447	security engineering workshop
   comp9491	applied ai
   comp9511	human computer interaction
   comp9514	advanced decision theory
   comp9515	pattern classification
   comp9517	computer vision
   comp9518	pattern recognition
   comp9519	multimedia systems
   comp9596	research project
   comp9614	linguistics
   comp9701	computer graphics using a gui
   comp9727	recommender systems
   comp9790	principles of gnss positioning
   comp9791	modern navigation &positioning
   comp9801	ext design&analysis of algo
   comp9814	ext artificial intelligence
   comp9833	ext computer networks & appl
   comp9844	ext neural networks
   comp9900	info tech project
   comp9901	p/t res. thesis comp sci & eng
   comp9902	res. thesis comp sci & eng f/t
   comp9910	mgt&com skills-compsci&eng res
   comp9912	project (24 uoc)
   comp9918	project report (90cr)
   comp9921	personal software process for
   comp9930	readings in comp sci and eng
   comp9945	research project
   comp9991	research project a
   comp9992	research project b
   comp9993	research project c
   crim3010	comparative criminal justice
   cven1015	computing
   cven1025	computing
   cven2002	engineering computations
   cven2025	engineering computations 1
   cven2702	engineering computations
   cven3015	engineering computations
   cven3025	engineering computations 2
   cven4307	steel & composite structures
   cven9820	computational struct mechanics
   cven9822	steel & composite structures
   cven9827	composite steel-concrete struc
   danc2000	dance analysis & composition 1
   danc2005	dance analysis & composition 2
   danc2015	dance analysis & composition 3
   dpde1005	architectural comp & modelling
   dpst1092	computer systems fundamentals
   ecoh4326	comparative iss in econ hist
   ecoh5357	comparative economic history
   econ3213	comparative forecasting techs
   econ5122	compet. in the know. econ.
   econ5255	computational stats & econ mod
   edst1492	computer skills for teachers
   edst2608	computers & teaching-learning
   edst2706	intro comp assisted instruct'n
   edst4092	computer skills for teachers
   edst4157	computing studies method 1
   edst4158	computing studies method 2
   edst5022	curr rsch on comps in instruct
   elec4343	source coding and compression
   elec4432	computer control &instrument'n
   elec4605	quantum devices and computers
   elec4632	computer control systems
   elec9401	computer control systems 1
   elec9402	computer control systems 2
   elec9403	real time computing & control
   elec9733	real computing and control
   engg1811	computing for engineers
   euro2302	the messiah complex
   expa1084	applied arts workshop 2 (compu
   expa2013	computer technology 1
   expa2014	computer technology 2
   expa3010	dance analysis & composition 1
   expa3011	dance analysis & composition 2
   expa3012	dance analysis & composition 3
   expa3013	dance analysis & composition 4
   expa3014	dance analysis & composition 5
   expa3015	dance analysis & composition 6
   expa4124	computer resources for artists
   expa5080	teach dance: improv'n&compos'n
   expa7748	composition studies 1
   expa7749	composition studies 2
   fibr2201	computing applications
   fins5553	insur. comp. oper. & manage.
   fins5582	mfinec research component
   fndn0301	computing studies
   fndn0302	computing studies and research
   fndn0303	computing for design
   fndn0304	computing for academic purpose
   fndn0305	computing for acad purpose h
   fndn0306	computing for acad purposes s
   fndn0311	computing studies - t
   fndn0312	computing academic purpose - t
   fndn0314	computing for design - t
   fndn0315	computing for acad purpose th
   fndn0316	computing for acad purp - ts
   food4220	computer applications
   food4320	computer applications
   food4537	computing in food science
   food9101	complex fluid micro & rheology
   gbat9131	leadership in a complex enviro
   gend1212	analysing a picture:comp.&des.
   gend4201	design and computing
   gene8001	computer game design
   genm0515	computers for professionals
   genp0515	computers for professionals
   gens2001	the computer
   gens5525	computer: impact, signif, uses
   gens9038	mathematics and computing 1
   gens9039	mathematics and computing 2
   gens9040	mathematics and computing 3
   gens9041	mathematics and computing 4
   gent0407	tv soaps: a comparative study
   gent0603	computer: impact, signif, uses
   gent0802	complexity of everyday life
   gent1003	computers into the 21st c
   genz1001	competition and innovation
   genz8501	computers in society
   geog3071	computer cartography
   geog3161	computer mapping &data display
   geog3861	computer mapping
   geog9014	computer mapping &data display
   geog9210	computer mapping &data display
   geol0300	computing&stats for geologists
   geol2041	geological computing
   geol9090	computing for groundwater spec
   gmat1111	introduction to computing
   gmat1150	survey methods& computations
   gmat1300	comp appl in geomatics
   gmat2111	principles of comp. processing
   gmat2112	principles of comp. processing
   gmat2122	computer graphics 1
   gmat2131	survey computations
   gmat2350	comp for spatial info sciences
   gmat2500	surveying computations a
   gmat2550	surveying computations b
   gmat3111	survey computations
   gmat3122	computer graphics 1
   gmat3231	geodetic computations
   gmat4111	data analysis and computing 1
   gmat4112	data analysis and computing 1
   gmat5111	data analysis and computing 2
   gmat5112	data analysis and computing 2
   gmat5122	computer graphics 2
   hdat9300	computing 4 hdat
   heal9471	comparative h'lth care systems
   heal9501	comp tech for health serv mngt
   heal9521	computer for postgraduates
   hist2046	contacts,culture & comparisons
   hist2487	the messiah complex
   hpsc2610	computers, brains & minds
   hpst2004	computers, brains and minds
   hpst2109	computers, brains & minds
   ides2121	introduction to computing
   ides3101	design studio 5: complexity
   ides3231	adv computer aided product des
   ides5153	computer graphic applications
   ides5154	computer aided design
   iest5009	competencies in sustainability
   iest5010	competencies in sustainability
   ilas0232	comp prog for info applic'ns
   ilas0233	computing applications in the
   infs1601	introduction to computing
   infs3607	distributed computer systems
   infs4858	managing complex projects
   inta1001	interior arch composition 1
   inta1002	interior arch composition 2
   inta1003	interior arch composition 3
   irob5732	spec topic- internat & comp ir
   irob5734	adv seminar-internat & comp ir
   jurd7419	competition law and policy
   jurd7468	aust legal system comp perspec
   jurd7473	asian competition law
   jurd7474	competition law and ip
   jurd7522	competition law
   jurd7546	law and tech comp perspectives
   jurd7549	child rights comp clinic
   jurd7603	global issues in comp policy
   jurd7610	mediation competition
   jurd7616	international & comparative ip
   jurd7648	transitional justice intl comp
   jurd7989	comparative anti-terrorism law
   jwst2104	the messiah complex
   kcme1107	intro comp&stats for geol &min
   kcme2104	appl'n of computers in mining
   land1131	intro to computer applications
   laws1032	computer applications to law
   laws2065	comparative law
   laws2085	comparative law
   laws2110	comparative constitutional law
   laws2148	harry gibbs moot comp 8uoc
   laws2149	harry gibbs moot comp
   laws2259	telecomm., competition & cons.
   laws2410	mediation competition
   laws2589	complex civil litigation
   laws2731	comparative criminal justice
   laws3009	comparative criminal justice:
   laws3022	competition law
   laws3035	developing comp apps to law
   laws3051	telecomm. competition & cons.
   laws3346	law and tech comp perspectives
   laws3348	transitional justice intl comp
   laws3368	aust legal system comp perspec
   laws3510	mediation competition
   laws3549	child rights comp clinic
   laws4016	international & comparative ip
   laws4019	competition law
   laws4089	comparative anti-terrorism law
   laws4120	themes in asian & compar. law
   laws4133	adv asian and comparative law
   laws4155	european union competition law
   laws4291	comparative constitutional law
   laws4609	develop computer apps to law
   laws4619	developing comp apps to law b
   laws4620	computer applications to law
   laws4765	complex commercial litigation
   laws5201	corporate compliance managment
   laws5231	competition law & regulation
   laws5234	competition law and regulation
   laws7003	global issues in comp policy
   laws7430	research component
   laws8016	international & comparative ip
   laws8073	asian competition law
   laws8074	competition law and ip
   laws8118	legal systems in comp persp
   laws8143	comparative patent law
   laws8144	comparative trade mark law
   laws8168	aust legal system comp perspec
   laws8203	global issues in comp policy
   laws8219	competition law and policy
   laws8289	comparative anti-terrorism law
   laws8346	law and tech comp perspectives
   laws8348	transitional justice intl comp
   laws8410	comparative law
   laws8765	complex commercial litigation
   laws9049	int. & comp. indigenous issues
   laws9875	comparative law
   laws9884	int & comp indig legal issues
   laws9973	comparative law
   laws9984	int & comp indig legal issues
   legt5531	comp. bus. & legal strategies
   legt5602	tax admin. & compliance
   libs0233	comp applications in info env
   libs0521	comp prog for bibliog systems
   manf3500	computers in manufacturing 1
   manf4500	computers in manufacturing 2
   manf4601	comp aided production mgmt a
   manf4602	comp aided production mgmt b
   manf8560	computer integrated manufact.
   manf9460	computer integrated manufact.
   manf9500	computer-aided progrmg for num
   manf9520	computer-aided manufacture
   manf9543	comp aided design/manufacture
   manf9560	computer integrated manufact.
   mark3022	computer applications in mktg
   mark7022	comp. applications in mktg
   math1061	introductory applied computing
   math2301	mathematical computing
   math2430	symbolic computing
   math2520	complex analysis
   math2521	complex analysis
   math2620	higher complex analysis
   math2621	higher complex analysis
   math2810	statistical computing
   math2910	higher statistical computing
   math3101	comp maths science & eng
   math3301	advanced math computing
   math3311	comp mathematics for finance
   math3400	logic and computability
   math3421	logic and computability
   math3430	symbolic computing
   math3680	higher complex analysis
   math3790	higher computat. combinatorics
   math3800	statistical computation 1
   math3810	statistical computation 2
   math3821	stat modelling & computing
   math3861	thry of stats 3 -stat'cal comp
   math3871	bayesian inference and comp
   math4003	maths and comp sci honours f/t
   math4004	maths and comp sci honours p/t
   math5009	comp'l coursework thesis ft
   math5010	comp'l coursework thesis pt
   math5245	computational fluid dynamics
   math5305	comp maths science & eng
   math5315	high perf numerical computing
   math5335	comp mathematics for finance
   math5400	logic and computability
   math5435	applied algebraic computation
   math5685	complex analysis
   math5856	intro to stats and stat comput
   math5960	bayesian inference & comput'n
   math9315	math computing(h perf num com)
   mats1021	computing in materials science
   mats1264	fibre reinf. plastic composite
   mats1274	metal&ceramic matrix composite
   mats1304	composite materials
   mats1364	composite and electronic matls
   mats3064	composite materials
   mats4005	composites and functional mats
   mats4174	metal matrix composites
   mats5342	comp modelling & design
   mats6110	computational materials
   mech1500	computing 1m
   mech3500	computing 2m
   mech3510	computing applications in mech
   mech3530	computing applcts in mech.sys.
   mech3540	computational engineering
   mech4130	computer-aided eng design
   mech4150	dsgn&maintenance of components
   mech4500	computing 3m
   mech4509	computing science for mech eng
   mech4620	computational fluid dynamics
   mech8620	computational fluid dynamics
   mech9130	computer-aided eng design
   mech9150	dsgn&maintenance of components
   mech9420	composite materials and mechan
   mech9620	computational fluid dynamics
   meft5103	computer media
   mgmt2106	comparative management systems
   mgmt3004	complexstrat&pol
   mgmt5802	comp. adv. through people
   mine0710	computing 1
   mine1720	microcomputers (mining)
   mine1730	computer application in mining
   mine3140	computational meth.in geomech.
   mine4082	computational methods
   mine4810	comp methods in geomechanics
   mngt0372	comparative management systems
   mngt0378	compensation & perf apppraisal
   mngt0533	special topics in computing
   mngt6584	complex adaptive leadership
   mtrn2500	comp for mtrn
   mtrn3500	comp appl in mechatronic sys
   mtrn3530	computing applcts in mech.sys.
   pfst2000	dance analysis & composition 1
   phcm9471	comparative h'lth care systems
   phcm9501	comp tech for health serv mngt
   phil5206	ai & computer science
   phil5207	ai and computer science 2a
   phys1601	comp. applic'ns in exp. sci. 1
   phys2001	mech & computational physics
   phys2020	computational physics
   phys2120	mechanics and computational
   phys2601	computer applications 2
   phys3601	comp. appl. in instrumentation
   phys3610	computational physics
   phys3620	comp. based signal processing
   plan1061	computer literacy
   plan2413	computers&information systems
   plan2414	computer applicat'n in plan 1
   plan3414	plann elect-comp app in plan 1
   pols2016	comparative pol. culture
   pols3953	comparative politics: russia
   psyc3191	computer science & psychology
   ptrl1013	computing-petroleum engineers
   ptrl4006	well completions & production
   ptrl4013	well completion & stimulation
   ptrl5016	well completions & stimulation
   ptrl6016	well completions & stimulation
   regs0010	numerical and computer methods
   regs0044	comp law in global context
   regs0067	competition law in a global
   regs0201	vector calculus and complex va
   regs0218	compliance: financial services
   regs0306	comparative constitutional law
   regs0368	comparative industrial law
   regs0370	comparative broadcasting law
   regs0373	competition law and policy
   regs0417	competition law and policy
   regs0428	comp. applic. in linguistics
   regs0453	multiple regress. & stat comp
   regs0474	comparative international tax
   regs0513	comparative competition law
   regs0541	comparative corporate taxation
   regs0545	computational fluid dynamics
   regs0633	comparative corp & comm law
   regs0638	international comparative corp
   regs0718	energy co-compliance in bldgs
   regs1073	theory of computation b
   regs1120	competitive intelligence
   regs2013	biochemistry: molecular compon
   regs3092	comp cntrl of machines & proc
   regs3265	intl and comparative ind. rel.
   regs3410	computer networks
   regs3419	competition law enforcement
   regs3446	comput'al method for stat.mod.
   regs3478	public companies
   regs3485	competition law
   regs3529	company law
   regs3557	comp mat in hazard mar environ
   regs3561	computers in business
   regs3568	issues in compet. advantages 2
   regs3576	issues in competitive advant i
   regs3598	company and commercial law
   regs3732	adv computerised legal res
   regs3761	companies and securities law
   regs3765	computerized legal inf systems
   regs3835	computer law
   regs3843	comparative law (a)
   regs3874	computer based info systems
   regs3886	strategic competitive advantag
   regs3895	companies and securities law
   regs3909	trade marks & unfair comp
   regs3948	competition law
   regs3966	comparative corporate governan
   regs4061	asian & comparative philosophy
   regs4356	comparative business-govt rels
   regs4973	principles of company law
   regs5004	statistical computation
   regs5109	company law
   regs5618	comp integrated manufacturing
   regs7309	competitive analysis
   regs7319	competitive marketing strat.
   regs7655	human rights & intl comp persp
   regs7726	composites & multiphase polyme
   regs7908	service managing for comp.adv.
   regs7961	computer networks & internets
   regs8008	computers in schools
   regs8102	computer organisation 1
   regs8126	client-server computing m
   regs8300	computers in school admin
   regs8488	company law
   regs8546	comparative intellectual prope
   regs8550	company law
   regs8957	comparative law
   regs9014	prof practicum comp sci & eng
   safe9122	computing in safety science
   sart1608	digital composite 1
   sart1681	multimedia computing elective1
   sart1810	introduction to computing
   sart2608	digital composite 2
   sart2681	multimedia computing elective2
   sart2811	multimedia computing workshop
   sart2833	figurative comp in painting
   sart2835	composition and design
   sart3608	digital composite 3
   sart3681	multimedia computing elective3
   sart3840	advanced multimedia computing
   sart9725	intro to multimedia computing
   sart9739	multimedia computing elective
   sart9741	composition and design
   sdes1106	design and computers 1
   sdes1110	design and computers 2
   sdes1111	integrated design computing 1
   sdes1211	integrated design computing 2
   sdes1601	colour,composition &typography
   sdes2107	design and computers 3
   sdes2115	design and computers 2b
   sdes3107	design and computers 4
   sdes4103	design and computers 4
   sdes6714	intro 3d computer aided design
   slst3211	computers in sports science
   slst4262	computer applications for rec.
   slst9896	computers in sports admin.
   slst9898	computers in exercise science
   soca3314	the messiah complex
   socf5112	complex practice issues
   soci3401	comp analysis of social data a
   soci3408	comp analysis of social data b
   soci5310	survey sampling & computer app
   socw7801	managing for compliance
   soma1608	digital composite
   soma1681	intro multimedia computing
   soma1810	introduction to computing
   soma2402	tangible computing
   soma2608	digital composite 2
   soma2681	advanced multimedia computing
   soma2811	multimedia computing workshop
   soma3415	compositional project
   soma3608	digital composite 3
   surv1111	introduction to computing
   surv2111	principles of comp. processing
   surv2122	computer graphics 1
   surv3111	survey computations
   surv3231	geodetic computations
   surv4111	data analysis and computing 1
   surv5111	data analysis and computing 2
   surv5122	computer graphics 2
   surv6121	computer graphics
   tabl1002	computer information systems
   tabl2053	acct for complex struct & inst
   tabl2731	competition and consumer law
   tabl3044	comparative tax systems
   tabl5543	bus company law
   tabl5544	comparative tax systems
   tedg0011	computers and teaching 2
   tedg0022	computers and teaching 3
   tedg1101	computers in education
   tedg1102	computers and teaching
   tedg1103	computers & the learning proc.
   tedg1104	issues in computer education
   tedg1106	comp-based res: design & prod
   tedg1107	managing with comps in schools
   tedg1108	teach. curric courses in comp
   tedg1112	computers - gifted & talented
   tedg1113	comp control tech in education
   tedg2022	computers and teaching 1
   tedg2031	computers in educational admin
   tedg5602	teach. curric courses in comp
   tedg5800	computers and education 1
   tedg5801	computers and education 2
   teed1134	fundamentals of computing
   teed2119	computers and people
   teed3149	curric w'shop: comps in class
   teed3173	comp. awareness & media stud.
   teed4322	curric w'shop: comps in class
   tele4343	source coding and compression
   tele9302	computer networks
   text2501	computing applications
   woms5930	feminist analysis & comp. apps
   woms5950	managing for compliance
   ymed3006	comparative health systems
   zacm3011	component design
   zacm3433	compressible flow
   zacm4020	computational structures
   zacm4031	compressible flow
   zacm4909	composite mechanics
   zacm4913	eng app of comp fluid dynamics
   zbus2200	markets and competition
   zeit1101	computational problem solving
   zeit1110	computer games
   zeit2102	computer technology
   zeit2104	computers and security
   zeit2305	computer games
   zeit3113	computer languages & algorithm
   zeit3304	computing proj - info sys
   zeit3307	computer games
   zeit4003	computational fluid dynamics
   zeit4103	computer science 4 (hons) f/t
   zeit7101	computational problem solving
   zeit8020	computer network operations
   zeit9100	computer science research f/t
   zeit9101	computer science research p/t
   zgen2300	computers in society
   zgen2301	computer games
   zhss8431	comparative defence planning
   zint1001	eng comp methods 1
   zite1001	computer tools for engineers
   zite1101	intro to computer science
   zite2101	computer languages & algorithm
   zite2102	computer technology
   zite3101	computing proj - comp sci
   zite3105	human computer interaction
   zite3106	interactive computer graphics
   zite3113	computer languages & algorithm
   zite3211	microcomputer interfacing
   zite3304	computing proj - info sys
   zite4103	computer science 4 (hons) f/t
   zite8104	computer security
   zite8145	softcomp
   zite9100	computer science research f/t
   zite9101	computer science research p/t
   zpem3302	complex variables
   ```

   ```
   grep -E -i comp course_codes.tsv
   ACIV2503	Eng Computational Meth 1A
   ACIV2504	Eng Computational Meth 1B
   ACIV2518	Eng Computational Methods 1
   ACIV3503	Eng Computational Methods 2A
   ACIV3504	Eng Computational Methods 2B
   ACIV3516	Eng Computational Methods 2
   ACMA2102	Eng Computational Methods 1
   ACMA3102	Eng Computational Methods 2
   ACMA4021	Computer Tools for Eng Mgt
   ACSC1100	Intro to Computer Science
   ACSC1401	Computer Tools for Engineers
   ACSC1501	Computer Tools for Engineers
   ACSC1502	Computer Prog for Engineers
   ACSC1600	Computer Science 1
   ACSC1800	Computer Science 1E
   ACSC2004	Comparative Prog Languages
   ACSC2009	Computer Speech Processing
   ACSC2013	Human Computer Interaction
   ACSC2015	Interactive Computer Graphics
   ACSC2018	Comp Tools for Decision Making
   ACSC2101	Computer Science Core 2A
   ACSC2102	Computer Science Core 2B
   ACSC2104	Computer Systems Architecture
   ACSC2106	Computer Languages & Algorithm
   ACSC2107	Computer Languages B
   ACSC2109	Computer Technology
   ACSC2405	Computer Architecture 2EE
   ACSC2601	Computer Science 2A
   ACSC2602	Computer Science 2B
   ACSC2800	Computer Science 2E
   ACSC2801	Computer Science 2CE
   ACSC2802	Computer Science 2EE
   ACSC2803	Computer Science 2AE
   ACSC2804	Computer Science 2ME
   ACSC3003	Computer Project
   ACSC3029	Computing Project 3
   ACSC3030	Cryptography & Comp Security 3
   ACSC3034	Human Computer Interaction 3
   ACSC3102	Human Computer Interaction
   ACSC3601	Computer Science 3A
   ACSC3603	Computer Science 3C
   ACSC4191	Computer Science 4 (Hons) F/T
   ACSC4501	Cryptog & Computer Security E
   ACSC4502	Computer Speech E
   ACSC4690	Computer Science 4 (Hon) F/T
   ACSC4691	Computer Science 4 (Hon) P/T
   ACSC7304	Computer Graphics
   ACSC7306	Computer Speech Processing
   ACSC7316	IT Spec Top 1: Comput Analysis
   ACSC7336	Computer Security
   ACSC7362	Distributed Computing
   ACSC8201	Intro to Computer and Info Sys
   ACSC8208	Comp Security & Cryptography
   ACSC8211	Computer Graphics
   ACSC8218	Computer Speech Processing
   ACSC8226	Evolutionary Computation
   ACSC8245	Comp Security & Cryptography
   ACSC8248	Computer Graphics
   ACSC8256	Comp Speech Processing
   ACSC9000	Computer Science Research F/T
   ACSC9001	Computer Science Research P/T
   AELE2007	Computer Design
   AELE2505	Computer Design
   AELE2508	Microcomputer Interfacing
   AELE3015	Computer Design
   AELE3021	Microcomputer Interfacing 1
   AELE3031	Microcomputer Interfacing
   AELE3509	Microcomputer Interfacing
   AELE4005	Microcomputer Interfacing A
   AELE4072	Computer Control Theory
   AELE4511	Computer Control Theory
   AMAT3026	Complex Analysis 3
   AMAT3107	Complex Variables
   AMAT3115	Scientific Computation
   AMAT3401	Complex Analysis 3E
   AMAT3503	Complex Variables E
   AMEC3023	Composites and Adhesives
   AMEC3512	Pumps, Turbines & Compressors
   AMEC4005	Composite Mechanics
   AMEC4019	Eng App of Comp Fluid Dynamics
   AMEC4046	Composite Mechanics
   ANCE8001	Computational Mathematics
   ANCE8002	Supercomputing Techniques
   ANCE8103	Fundamental Applied Computat'n
   ANCE8105	Computational Techniques
   ANCE9105	Comp Techniques Fluid Dynamics
   APHY3028	Computational Physics
   APHY3041	Computational Physics
   APHY3113	Computational Physics
   APHY3120	Computers & Electronics in Phy
   APHY4003	Microcomp. Appl. in Adv. Mats.
   APOL2617	Intro to Comparative Politics
   APOL3621	Intro to Comparative Politics
   ARCH1391	Digital Computation Studio
   ARCH5200	Computer Graphics Programming
   ARCH5201	Computer Applications 1
   ARCH5202	Computer Applications 2
   ARCH5203	Computer Applications 3
   ARCH5205	Theory of Arch Computing
   ARCH5220	Computer Graphics Programming
   ARCH5221	Computer Graphics Programming
   ARCH5222	Computer Applications 1
   ARCH5223	Computer Applications 2
   ARCH5940	Theory of Arch Computing 1
   ARCH5941	Theory of Arch Computing 2
   ARCH5942	Arch Computing Seminar
   ARCH5943	Theory of Arch Computing
   ARCH6201	Architectural Computing 1
   ARCH6205	Architectural Computing 2
   ARCH6214	Architectural Computing 2
   ARCH7204	Design Computing Theory
   ARCH7205	Computer Graphics Programming
   ARCH7221	Computer Modelling & Rendering
   ARTS2301	Computers, Brains & Minds
   ATAX0002	Computer Information Systems
   ATAX0053	Acct for Complex Struct & Inst
   ATAX0324	GST: Complex Issues & Planning
   ATAX0341	Comparative Tax Systems
   ATAX0424	GST: Complex Issues & Planning
   ATAX0441	Comparative Tax Systems
   ATAX0641	Comparative Tax Systems
   ATAX0903	Legal Comp Database Research
   ATAX0904	Computer Based Acc Spreadsheet
   ATAX0907	Computer Database
   AUST2002	Aboriginal Stud: Global Comp 1
   AUST2003	Aboriginal Stud: Global Comp 2
   AVEN1500	Computing for Aviation
   BEIL0003	BE Annual Design Competition
   BEIL0004	Design Competitions and Bids
   BENV1141	Computers and Information Tech
   BENV1242	Computer-Aided Design
   BENV2405	Computer Graphics Programming
   BENV2406	Design and Computation
   BENV7503	Geocomputation
   BINF3020	Computational Bioinformatics
   BINF9020	Computational Bioinformatics
   BIOM5912	Comp Thesis B&C
   BIOM5920	Thesis Part A (Comp)
   BIOM5921	Thesis Part B (Comp)
   BIOM9332	Biocompatibility
   BIOM9334	Comprehensive Biomaterials SCI
   BIOM9501	Computing for Biomedical Eng
   BIOM9601	Biomed Applic.of Microcomp 1
   BIOM9602	Biomed Applic.of Microcomp 2
   BIOS3021	Comparative Animal Physiology
   BLDG2281	Introduction to Computing
   BLDG3282	Computer Apps in Building
   BLDG5103	Computers in Management
   BLDG6155	Computers in Construction Mgmt
   CEIC5310	Comp Studies in Process Ind
   CEIC5335	Adv Comp Methods Process Ind
   CEIC6711	Complex Fluids
   CEIC8310	Computing Studies Proc Ind
   CHEM3031	Inorg Chem:Trans Metals & Comp
   CHEM3640	Computers in Chemistry
   CIVL1015	Computing
   CIVL1106	Computing & Graphics
   CIVL3015	Engineering Computations
   CIVL3106	Engineering Computations
   CIVL9820	Computational Structural Mech
   CMED9517	Adv Biostatistic & Stat Comp
   CMED9520	Intro Stat Comp & Stats in Epi
   CODE1110	Computational Design Theory 1
   CODE1150	Computational Design I
   CODE1210	Computational Design Theory 2
   CODE1231	Urban Computing
   CODE1240	Computational Design 1
   CODE2110	Computational Design Theory 3
   CODE2121	Advanced Computational Design
   CODE2132	Computational Design 3 (Urban)
   COFA1531	Studio Research -M'Media Comp1
   COFA1533	Studio Research -M'Media Comp3
   COFA2078	Studio Research Basic Comp
   COFA2080	Std Research Composition&Des
   COFA2680	Multi-Media Computing Unit 1
   COFA2681	Multi-Media Computing Unit 2
   COFA2682	Multi-Media Computing Unit 3
   COFA2683	Multi-Media Computing Unit 4
   COFA2684	Multi-Media Computing Unit 5
   COFA3680	M'Media Computing Unit 1(Elec)
   COFA3681	Multimedia Computing Elective1
   COFA3682	Multimedia Computing Elective2
   COFA3810	Introduction to Computing
   COFA3811	Multimedia Computing Workshop
   COFA3835	Composition & Design Workshop
   COFA3840	Advanced Multi-media Computing
   COFA4036	The Computer&the Art Educator
   COFA5106	Design & Comp: An Introduction
   COFA5116	Design and Computers 1
   COFA5130	Typography and Composition
   COFA5208	Design & Computers:2D & 3D Cad
   COFA5216	Design and Computers 1
   COFA5240	Design and Computers 2 Cad
   COFA5241	Design & Computers 2 Graphics
   COFA5308	Design and Timebased Computer
   COFA5315	Design and Computers 2
   COFA5338	Design and Computers 3 - Cad
   COFA5339	Design&Computers 3 - Graphics
   COFA5434	Design and Computers 4
   COFA6315	Design and Computers S2 Only
   COFA7006	Applied Arts Wshop 2-Comp Tech
   COFA7051	Computer Technology 1
   COFA7052	Computer Technology 2
   COFA8670	Intro to Multimedia Computing
   COFA9058	MAE Elective(Design&Computers)
   COMD1000	Intro to Comparative Develop't
   COMM8004	Becoming a Complete Scholar
   COMP0001	Quality Management
   COMP0011	Fundamentals of Computing
   COMP1000	Web, Spreadsheets & Databases
   COMP1001	Introduction to Computing
   COMP1010	The Art of Computing
   COMP1011	Computing 1A
   COMP1021	Computing 1B
   COMP1081	Harnessing the Power of IT
   COMP1091	Solving Problems with Software
   COMP1400	Programming for Designers
   COMP1511	Programming Fundamentals
   COMP1521	Computer Systems Fundamentals
   COMP1531	Software Eng Fundamentals
   COMP1711	Higher Computing 1A
   COMP1721	Higher Computing 1B
   COMP1811	Computing 1 (Procedural)
   COMP1821	Computing 2
   COMP1911	Computing 1A
   COMP1917	Computing 1
   COMP1921	Computing 1B
   COMP1927	Computing 2
   COMP2011	Data Organisation
   COMP2021	Digital System Structures
   COMP2031	Concurrent Computing
   COMP2041	Software Construction
   COMP2091	Computing 2
   COMP2110	Software System Specification
   COMP2111	System Modelling and Design
   COMP2121	Microprocessors & Interfacing
   COMP2411	Logic and Logic Programming
   COMP2511	O-O Design & Programming
   COMP2521	Data Structures and Algorithms
   COMP2711	Higher Data Organisation
   COMP2811	Computing B
   COMP2911	Eng. Design in Computing
   COMP2920	Professional Issues and Ethics
   COMP3111	Software Engineering
   COMP3120	Introduction to Algorithms
   COMP3121	Algorithms & Programming Tech
   COMP3131	Programming Languages & Compil
   COMP3141	Software Sys Des&Implementat'n
   COMP3151	Foundations of Concurrency
   COMP3152	Comparative Concurrency Semant
   COMP3153	Algorithmic Verification
   COMP3161	Concepts of Programming Lang.
   COMP3171	Object-Oriented Programming
   COMP3211	Computer Architecture
   COMP3221	Microprocessors & Embedded Sys
   COMP3222	Digital Circuits and Systems
   COMP3231	Operating Systems
   COMP3241	Real Time Systems
   COMP3311	Database Systems
   COMP3331	Computer Networks&Applications
   COMP3411	Artificial Intelligence
   COMP3421	Computer Graphics
   COMP3431	Robotic Software Architecture
   COMP3441	Security Engineering
   COMP3511	Human Computer Interaction
   COMP3601	Design Project A
   COMP3710	Software Project Management
   COMP3711	Software Project Management
   COMP3720	Total Quality Management
   COMP3821	Ext Algorithms&Prog Techniques
   COMP3891	Ext Operating Systems
   COMP3900	Computer Science Project
   COMP3901	Special Project A
   COMP3902	Special Project B
   COMP3931	Ext Computer Networks & App
   COMP4001	Object-Oriented Software Dev
   COMP4002	Logic Synthesis & Verification
   COMP4003	Industrial Software Developmen
   COMP4011	Web Applications Engineering
   COMP4012	Occasional Elec S2 - Comp.Eng.
   COMP4022	Theory of Neural Nets
   COMP4111	Distributed Object Sys & Tech
   COMP4121	Advanced Algorithms
   COMP4128	Programming Challenges
   COMP4131	Programming Language Semantics
   COMP4132	Adv. Functional Programming
   COMP4133	Advanced Compiler Construction
   COMP4141	Theory of Computation
   COMP4151	Algorithmic Verification
   COMP4161	Advanced Verification
   COMP4181	Language-based Software Safety
   COMP4211	Adv Architectures & Algorithms
   COMP4215	Vlsi Systems Architecture and
   COMP4216	Distributed Operating Systems
   COMP4314	Next Generation Database Systs
   COMP4317	XML and Databases
   COMP4335	Wireless Mesh&Sensor Networks
   COMP4336	Mobile Data Networking
   COMP4337	Securing Fixed & Wireless Netw
   COMP4411	Experimental Robotics
   COMP4412	Introduction to Modal Logic
   COMP4415	First-order Logic
   COMP4416	Intelligent Agents
   COMP4418	Knowledge Representation
   COMP4431	Game Design Workshop
   COMP4442	Advanced Computer Security
   COMP4444	Neural Networks
   COMP4511	User Interface Design & Constr
   COMP4601	Design Project B
   COMP4903	Industrial Training (B.E.)
   COMP4904	Industrial Training 1
   COMP4905	Industrial Training 2
   COMP4906	Industrial Training 3
   COMP4910	Thesis Part A
   COMP4911	Thesis Part B
   COMP4913	Computer Science 4 Honours P/T
   COMP4914	Computer Science 4 Honours F/T
   COMP4920	Professional Issues and Ethics
   COMP4930	Thesis Part A
   COMP4931	Thesis Part B
   COMP4941	Thesis Part B
   COMP4951	Research Thesis A
   COMP4952	Research Thesis B
   COMP4953	Research Thesis C
   COMP4961	Computer Science Thesis A
   COMP4962	Computer Science Thesis B
   COMP4963	Computer Science Thesis C
   COMP6080	Web Front-End Programming
   COMP6324	IoT Services Engineering
   COMP6441	Security Engineering
   COMP6443	Web Application Security
   COMP6445	Digital Forensics
   COMP6447	Security Assessment
   COMP6448	Security Masterclass
   COMP6451	Cryptocurrency and DLT
   COMP6452	Blockchain App Architecture
   COMP6714	Info Retrieval and Web Search
   COMP6721	(In-)Formal Methods
   COMP6731	Combinatorial Data Processing
   COMP6733	Internet of Things
   COMP6741	Algorithms for Intractable Pbs
   COMP6752	Modelling Concurrent Systems
   COMP6771	Advanced C++ Programming
   COMP6841	Extended Security Engineering
   COMP6843	Extended WebApp Security
   COMP6845	Extended Digital Forensics
   COMP6991	Modern Prog Problems with Rust
   COMP8524	Postgraduate Elective 24 UOC
   COMP9000	Special Program
   COMP9001	E-Commerce Technologies
   COMP9002	XML and Databases
   COMP9008	Software Engineering
   COMP9009	Adv Topics in Software Eng
   COMP9011	Literacy and Programming
   COMP9012	Software Engineering and Tools
   COMP9013	Data Bases and Expert Systems
   COMP9014	Comp Organizat'n & Interfacing
   COMP9015	Issues in Computing
   COMP9018	Advanced Graphics
   COMP9020	Foundations of Comp. Science
   COMP9021	Principles of Programming
   COMP9022	Digital Systems Structures
   COMP9023	Functional Programming
   COMP9024	Data Structures & Algorithms
   COMP9031	Internet Programming
   COMP9032	Microprocessors & Interfacing
   COMP9041	Software Construction
   COMP9044	Software Construction
   COMP9081	Harnessing the Power of IT
   COMP9101	Design &Analysis of Algorithms
   COMP9102	Programming Lang & Compilers
   COMP9103	Algorithms & Comp. Complexity
   COMP9114	Formal Specification
   COMP9115	Prog Languages: Fund. Concepts
   COMP9116	S'ware Dev: B-Meth & B-Toolkit
   COMP9117	Software Architecture
   COMP9151	Foundations of Concurrency
   COMP9152	Comparative Concurrency Semant
   COMP9153	Algorithmic Verification
   COMP9154	Foundations of Concurrency
   COMP9161	Concepts of Programming Lang.
   COMP9164	Concepts of Programming Lang.
   COMP9171	Object-Oriented Programming
   COMP9181	Language-based Software Safety
   COMP9201	Operating Systems
   COMP9211	Computer Architecture
   COMP9214	Computer Org. & Architecture
   COMP9215	Vlsi System Design
   COMP9216	Parallel &Distributed Comp Sys
   COMP9221	Microprocessors & Embedded Sys
   COMP9222	Digital Circuits and Systems
   COMP9231	Integrated Digital Systems
   COMP9241	Supercomputing Techniques
   COMP9242	Advanced Operating Systems
   COMP9243	Distributed Systems
   COMP9244	Software View of Proc Architec
   COMP9245	Real-Time Systems
   COMP9283	Ext Operating Systems
   COMP9301	Cyber Security Project
   COMP9302	Cyber Security Project B
   COMP9311	Database Systems
   COMP9312	Data Analytics for Graphs
   COMP9313	Big Data Management
   COMP9314	Next Generation Database Systs
   COMP9315	Database Systems Implementat'n
   COMP9316	eCommerce Implementation
   COMP9317	XML and Databases
   COMP9318	Data Warehousing & Data Mining
   COMP9319	Web Data Compression & Search
   COMP9321	Data Services Engineering
   COMP9322	Software Service Design & Eng
   COMP9323	e-Enterprise Project
   COMP9331	Computer Networks&Applications
   COMP9332	Network Routing and Switching
   COMP9333	Advanced Computer Networks
   COMP9334	Systems Capacity Planning
   COMP9335	Wireless Mesh&Sensor Networks
   COMP9336	Mobile Data Networking
   COMP9337	Securing Fixed & Wireless Netw
   COMP9414	Artificial Intelligence
   COMP9415	Computer Graphics
   COMP9416	Knowledge Based Systems
   COMP9417	Machine Learning & Data Mining
   COMP9418	Advanced Machine Learning
   COMP9431	Robotic Software Architecture
   COMP9434	Robotic Software Architecture
   COMP9441	Security Engineering
   COMP9444	Neural Networks, Deep Learning
   COMP9447	Security Engineering Workshop
   COMP9491	Applied AI
   COMP9511	Human Computer Interaction
   COMP9514	Advanced Decision Theory
   COMP9515	Pattern Classification
   COMP9517	Computer Vision
   COMP9518	Pattern Recognition
   COMP9519	Multimedia Systems
   COMP9596	Research Project
   COMP9614	Linguistics
   COMP9701	Computer Graphics Using a Gui
   COMP9727	Recommender Systems
   COMP9790	Principles of GNSS Positioning
   COMP9791	Modern Navigation &Positioning
   COMP9801	Ext Design&Analysis of Algo
   COMP9814	Ext Artificial Intelligence
   COMP9833	Ext Computer Networks & Appl
   COMP9844	Ext Neural Networks
   COMP9900	Info Tech Project
   COMP9901	P/T Res. Thesis Comp Sci & Eng
   COMP9902	Res. Thesis Comp Sci & Eng F/T
   COMP9910	Mgt&Com Skills-CompSci&Eng Res
   COMP9912	Project (24 UOC)
   COMP9918	Project Report (90Cr)
   COMP9921	Personal Software Process for
   COMP9930	Readings in Comp Sci and Eng
   COMP9945	Research Project
   COMP9991	Research Project A
   COMP9992	Research Project B
   COMP9993	Research Project C
   CRIM3010	Comparative Criminal Justice
   CVEN1015	Computing
   CVEN1025	Computing
   CVEN2002	Engineering Computations
   CVEN2025	Engineering Computations 1
   CVEN2702	Engineering Computations
   CVEN3015	Engineering Computations
   CVEN3025	Engineering Computations 2
   CVEN4307	Steel & Composite Structures
   CVEN9820	Computational Struct Mechanics
   CVEN9822	Steel & Composite Structures
   CVEN9827	Composite Steel-Concrete Struc
   DANC2000	Dance Analysis & Composition 1
   DANC2005	Dance Analysis & Composition 2
   DANC2015	Dance Analysis & Composition 3
   DPDE1005	Architectural Comp & Modelling
   DPST1092	Computer Systems Fundamentals
   ECOH4326	Comparative Iss in Econ Hist
   ECOH5357	Comparative Economic History
   ECON3213	Comparative Forecasting Techs
   ECON5122	Compet. in the Know. Econ.
   ECON5255	Computational Stats & Econ Mod
   EDST1492	Computer Skills for Teachers
   EDST2608	Computers & Teaching-Learning
   EDST2706	Intro Comp Assisted Instruct'n
   EDST4092	Computer Skills for Teachers
   EDST4157	Computing Studies Method 1
   EDST4158	Computing Studies Method 2
   EDST5022	Curr Rsch on Comps in Instruct
   ELEC4343	Source Coding and Compression
   ELEC4432	Computer Control &Instrument'n
   ELEC4605	Quantum Devices and Computers
   ELEC4632	Computer Control Systems
   ELEC9401	Computer Control Systems 1
   ELEC9402	Computer Control Systems 2
   ELEC9403	Real Time Computing & Control
   ELEC9733	Real Computing and Control
   ENGG1811	Computing for Engineers
   EURO2302	The Messiah Complex
   EXPA1084	Applied Arts Workshop 2 (Compu
   EXPA2013	Computer Technology 1
   EXPA2014	Computer Technology 2
   EXPA3010	Dance Analysis & Composition 1
   EXPA3011	Dance Analysis & Composition 2
   EXPA3012	Dance Analysis & Composition 3
   EXPA3013	Dance Analysis & Composition 4
   EXPA3014	Dance Analysis & Composition 5
   EXPA3015	Dance Analysis & Composition 6
   EXPA4124	Computer Resources for Artists
   EXPA5080	Teach Dance: Improv'n&Compos'n
   EXPA7748	Composition Studies 1
   EXPA7749	Composition Studies 2
   FIBR2201	Computing Applications
   FINS5553	Insur. Comp. Oper. & Manage.
   FINS5582	MFinEc Research Component
   FNDN0301	Computing Studies
   FNDN0302	Computing Studies and Research
   FNDN0303	Computing for Design
   FNDN0304	Computing for Academic Purpose
   FNDN0305	Computing for Acad Purpose H
   FNDN0306	Computing for Acad Purposes S
   FNDN0311	Computing Studies - T
   FNDN0312	Computing Academic Purpose - T
   FNDN0314	Computing for Design - T
   FNDN0315	Computing for Acad Purpose TH
   FNDN0316	Computing for Acad Purp - TS
   FOOD4220	Computer Applications
   FOOD4320	Computer Applications
   FOOD4537	Computing in Food Science
   FOOD9101	Complex Fluid Micro & Rheology
   GBAT9131	Leadership in a Complex Enviro
   GEND1212	Analysing a Picture:Comp.&Des.
   GEND4201	Design and Computing
   GENE8001	Computer Game Design
   GENM0515	Computers for Professionals
   GENP0515	Computers for Professionals
   GENS2001	The Computer
   GENS5525	Computer: Impact, Signif, Uses
   GENS9038	Mathematics and Computing 1
   GENS9039	Mathematics and Computing 2
   GENS9040	Mathematics and Computing 3
   GENS9041	Mathematics and Computing 4
   GENT0407	TV Soaps: A Comparative Study
   GENT0603	Computer: Impact, Signif, Uses
   GENT0802	Complexity of Everyday Life
   GENT1003	Computers into the 21st C
   GENZ1001	Competition and Innovation
   GENZ8501	Computers in Society
   GEOG3071	Computer Cartography
   GEOG3161	Computer Mapping &Data Display
   GEOG3861	Computer Mapping
   GEOG9014	Computer Mapping &Data Display
   GEOG9210	Computer Mapping &Data Display
   GEOL0300	Computing&Stats for Geologists
   GEOL2041	Geological Computing
   GEOL9090	Computing for Groundwater Spec
   GMAT1111	Introduction to Computing
   GMAT1150	Survey Methods& Computations
   GMAT1300	Comp Appl in Geomatics
   GMAT2111	Principles of Comp. Processing
   GMAT2112	Principles of Comp. Processing
   GMAT2122	Computer Graphics 1
   GMAT2131	Survey Computations
   GMAT2350	Comp for Spatial Info Sciences
   GMAT2500	Surveying Computations A
   GMAT2550	Surveying Computations B
   GMAT3111	Survey Computations
   GMAT3122	Computer Graphics 1
   GMAT3231	Geodetic Computations
   GMAT4111	Data Analysis and Computing 1
   GMAT4112	Data Analysis and Computing 1
   GMAT5111	Data Analysis and Computing 2
   GMAT5112	Data Analysis and Computing 2
   GMAT5122	Computer Graphics 2
   HDAT9300	Computing 4 HDAT
   HEAL9471	Comparative H'lth Care Systems
   HEAL9501	Comp Tech for Health Serv Mngt
   HEAL9521	Computer for Postgraduates
   HIST2046	Contacts,Culture & Comparisons
   HIST2487	The Messiah Complex
   HPSC2610	Computers, Brains & Minds
   HPST2004	Computers, Brains and Minds
   HPST2109	Computers, Brains & Minds
   IDES2121	Introduction to Computing
   IDES3101	Design Studio 5: Complexity
   IDES3231	Adv Computer Aided Product Des
   IDES5153	Computer Graphic Applications
   IDES5154	Computer Aided Design
   IEST5009	Competencies in Sustainability
   IEST5010	Competencies in Sustainability
   ILAS0232	Comp Prog for Info Applic'ns
   ILAS0233	Computing Applications in the
   INFS1601	Introduction to Computing
   INFS3607	Distributed Computer Systems
   INFS4858	Managing Complex Projects
   INTA1001	Interior Arch Composition 1
   INTA1002	Interior Arch Composition 2
   INTA1003	Interior Arch Composition 3
   IROB5732	Spec Topic- Internat & Comp IR
   IROB5734	Adv Seminar-Internat & Comp IR
   JURD7419	Competition Law and Policy
   JURD7468	Aust Legal System Comp Perspec
   JURD7473	Asian Competition Law
   JURD7474	Competition Law and IP
   JURD7522	Competition Law
   JURD7546	Law and Tech Comp Perspectives
   JURD7549	Child Rights Comp Clinic
   JURD7603	Global Issues in Comp Policy
   JURD7610	Mediation Competition
   JURD7616	International & Comparative IP
   JURD7648	Transitional Justice Intl Comp
   JURD7989	Comparative Anti-Terrorism Law
   JWST2104	The Messiah Complex
   KCME1107	Intro Comp&Stats for Geol &Min
   KCME2104	Appl'n of Computers in Mining
   LAND1131	Intro to Computer Applications
   LAWS1032	Computer Applications to Law
   LAWS2065	Comparative Law
   LAWS2085	Comparative Law
   LAWS2110	Comparative Constitutional Law
   LAWS2148	Harry Gibbs Moot Comp 8uoc
   LAWS2149	Harry Gibbs Moot Comp
   LAWS2259	Telecomm., Competition & Cons.
   LAWS2410	Mediation Competition
   LAWS2589	Complex Civil Litigation
   LAWS2731	Comparative Criminal Justice
   LAWS3009	Comparative Criminal Justice:
   LAWS3022	Competition Law
   LAWS3035	Developing Comp Apps to Law
   LAWS3051	Telecomm. Competition & Cons.
   LAWS3346	Law and Tech Comp Perspectives
   LAWS3348	Transitional Justice Intl Comp
   LAWS3368	Aust Legal System Comp Perspec
   LAWS3510	Mediation Competition
   LAWS3549	Child Rights Comp Clinic
   LAWS4016	International & Comparative IP
   LAWS4019	Competition Law
   LAWS4089	Comparative Anti-Terrorism Law
   LAWS4120	Themes in Asian & Compar. Law
   LAWS4133	Adv Asian and Comparative Law
   LAWS4155	European Union Competition Law
   LAWS4291	Comparative Constitutional Law
   LAWS4609	Develop Computer Apps to Law
   LAWS4619	Developing Comp Apps to Law B
   LAWS4620	Computer Applications to Law
   LAWS4765	Complex Commercial Litigation
   LAWS5201	Corporate Compliance Managment
   LAWS5231	Competition Law & Regulation
   LAWS5234	Competition Law and Regulation
   LAWS7003	Global Issues in Comp Policy
   LAWS7430	Research Component
   LAWS8016	International & Comparative IP
   LAWS8073	Asian Competition Law
   LAWS8074	Competition Law and IP
   LAWS8118	Legal Systems in Comp Persp
   LAWS8143	Comparative Patent Law
   LAWS8144	Comparative Trade Mark Law
   LAWS8168	Aust Legal System Comp Perspec
   LAWS8203	Global Issues in Comp Policy
   LAWS8219	Competition Law and Policy
   LAWS8289	Comparative Anti-Terrorism Law
   LAWS8346	Law and Tech Comp Perspectives
   LAWS8348	Transitional Justice Intl Comp
   LAWS8410	Comparative Law
   LAWS8765	Complex Commercial Litigation
   LAWS9049	Int. & Comp. Indigenous Issues
   LAWS9875	Comparative Law
   LAWS9884	Int & Comp Indig Legal Issues
   LAWS9973	Comparative Law
   LAWS9984	Int & Comp Indig Legal Issues
   LEGT5531	Comp. Bus. & Legal Strategies
   LEGT5602	Tax Admin. & Compliance
   LIBS0233	Comp Applications in Info Env
   LIBS0521	Comp Prog for Bibliog Systems
   MANF3500	Computers in Manufacturing 1
   MANF4500	Computers in Manufacturing 2
   MANF4601	Comp Aided Production Mgmt A
   MANF4602	Comp Aided Production Mgmt B
   MANF8560	Computer Integrated Manufact.
   MANF9460	Computer Integrated Manufact.
   MANF9500	Computer-Aided Progrmg for Num
   MANF9520	Computer-Aided Manufacture
   MANF9543	Comp Aided Design/Manufacture
   MANF9560	Computer Integrated Manufact.
   MARK3022	Computer Applications in Mktg
   MARK7022	Comp. Applications in Mktg
   MATH1061	Introductory Applied Computing
   MATH2301	Mathematical Computing
   MATH2430	Symbolic Computing
   MATH2520	Complex Analysis
   MATH2521	Complex Analysis
   MATH2620	Higher Complex Analysis
   MATH2621	Higher Complex Analysis
   MATH2810	Statistical Computing
   MATH2910	Higher Statistical Computing
   MATH3101	Comp Maths Science & Eng
   MATH3301	Advanced Math Computing
   MATH3311	Comp Mathematics for Finance
   MATH3400	Logic and Computability
   MATH3421	Logic and Computability
   MATH3430	Symbolic Computing
   MATH3680	Higher Complex Analysis
   MATH3790	Higher Computat. Combinatorics
   MATH3800	Statistical Computation 1
   MATH3810	Statistical Computation 2
   MATH3821	Stat Modelling & Computing
   MATH3861	Thry of Stats 3 -Stat'cal Comp
   MATH3871	Bayesian Inference and Comp
   MATH4003	Maths and Comp Sci Honours F/T
   MATH4004	Maths and Comp Sci Honours P/T
   MATH5009	Comp'l Coursework Thesis FT
   MATH5010	Comp'l Coursework Thesis PT
   MATH5245	Computational Fluid Dynamics
   MATH5305	Comp Maths Science & Eng
   MATH5315	High Perf Numerical Computing
   MATH5335	Comp Mathematics for Finance
   MATH5400	Logic and Computability
   MATH5435	Applied Algebraic Computation
   MATH5685	Complex Analysis
   MATH5856	Intro to Stats and Stat Comput
   MATH5960	Bayesian Inference & Comput'n
   MATH9315	Math Computing(H Perf Num Com)
   MATS1021	Computing in Materials Science
   MATS1264	Fibre Reinf. Plastic Composite
   MATS1274	Metal&Ceramic Matrix Composite
   MATS1304	Composite Materials
   MATS1364	Composite and Electronic Matls
   MATS3064	Composite Materials
   MATS4005	Composites and Functional Mats
   MATS4174	Metal Matrix Composites
   MATS5342	Comp Modelling & Design
   MATS6110	Computational Materials
   MECH1500	Computing 1M
   MECH3500	Computing 2M
   MECH3510	Computing Applications in Mech
   MECH3530	Computing Applcts in Mech.Sys.
   MECH3540	Computational Engineering
   MECH4130	Computer-Aided Eng Design
   MECH4150	Dsgn&Maintenance of Components
   MECH4500	Computing 3M
   MECH4509	Computing Science for Mech Eng
   MECH4620	Computational Fluid Dynamics
   MECH8620	Computational Fluid Dynamics
   MECH9130	Computer-Aided Eng Design
   MECH9150	Dsgn&Maintenance of Components
   MECH9420	Composite Materials and Mechan
   MECH9620	Computational Fluid Dynamics
   MEFT5103	Computer Media
   MGMT2106	Comparative Management Systems
   MGMT3004	ComplexStrat&Pol
   MGMT5802	Comp. Adv. Through People
   MINE0710	Computing 1
   MINE1720	Microcomputers (Mining)
   MINE1730	Computer Application in Mining
   MINE3140	Computational Meth.in Geomech.
   MINE4082	Computational Methods
   MINE4810	Comp Methods in Geomechanics
   MNGT0372	Comparative Management Systems
   MNGT0378	Compensation & Perf Apppraisal
   MNGT0533	Special Topics in Computing
   MNGT6584	Complex Adaptive Leadership
   MTRN2500	Comp for MTRN
   MTRN3500	Comp Appl in Mechatronic Sys
   MTRN3530	Computing Applcts in Mech.Sys.
   PFST2000	Dance Analysis & Composition 1
   PHCM9471	Comparative H'lth Care Systems
   PHCM9501	Comp Tech for Health Serv Mngt
   PHIL5206	AI & Computer Science
   PHIL5207	AI and Computer Science 2A
   PHYS1601	Comp. Applic'ns in Exp. Sci. 1
   PHYS2001	Mech & Computational Physics
   PHYS2020	Computational Physics
   PHYS2120	Mechanics and Computational
   PHYS2601	Computer Applications 2
   PHYS3601	Comp. Appl. in Instrumentation
   PHYS3610	Computational Physics
   PHYS3620	Comp. Based Signal Processing
   PLAN1061	Computer Literacy
   PLAN2413	Computers&Information Systems
   PLAN2414	Computer Applicat'n in Plan 1
   PLAN3414	Plann Elect-Comp App in Plan 1
   POLS2016	Comparative Pol. Culture
   POLS3953	Comparative Politics: Russia
   PSYC3191	Computer Science & Psychology
   PTRL1013	Computing-Petroleum Engineers
   PTRL4006	Well Completions & Production
   PTRL4013	Well Completion & Stimulation
   PTRL5016	Well Completions & Stimulation
   PTRL6016	Well Completions & Stimulation
   REGS0010	Numerical and Computer Methods
   REGS0044	Comp Law in Global Context
   REGS0067	Competition Law in a Global
   REGS0201	Vector Calculus and Complex Va
   REGS0218	Compliance: Financial Services
   REGS0306	Comparative Constitutional Law
   REGS0368	Comparative Industrial Law
   REGS0370	Comparative Broadcasting Law
   REGS0373	Competition Law and Policy
   REGS0417	Competition Law and Policy
   REGS0428	Comp. Applic. in Linguistics
   REGS0453	Multiple Regress. & Stat Comp
   REGS0474	Comparative International Tax
   REGS0513	Comparative Competition Law
   REGS0541	Comparative Corporate Taxation
   REGS0545	Computational Fluid Dynamics
   REGS0633	Comparative Corp & Comm Law
   REGS0638	International Comparative Corp
   REGS0718	Energy Co-Compliance in Bldgs
   REGS1073	Theory of Computation B
   REGS1120	Competitive Intelligence
   REGS2013	Biochemistry: Molecular Compon
   REGS3092	Comp Cntrl of Machines & Proc
   REGS3265	Intl and Comparative Ind. Rel.
   REGS3410	Computer Networks
   REGS3419	Competition Law Enforcement
   REGS3446	Comput'al Method for Stat.Mod.
   REGS3478	Public Companies
   REGS3485	Competition Law
   REGS3529	Company Law
   REGS3557	Comp Mat in Hazard Mar Environ
   REGS3561	Computers in Business
   REGS3568	Issues in Compet. Advantages 2
   REGS3576	Issues in Competitive Advant I
   REGS3598	Company and Commercial Law
   REGS3732	Adv Computerised Legal Res
   REGS3761	Companies and Securities Law
   REGS3765	Computerized Legal Inf Systems
   REGS3835	Computer Law
   REGS3843	Comparative Law (A)
   REGS3874	Computer Based Info Systems
   REGS3886	Strategic Competitive Advantag
   REGS3895	Companies and Securities Law
   REGS3909	Trade Marks & Unfair Comp
   REGS3948	Competition Law
   REGS3966	Comparative Corporate Governan
   REGS4061	Asian & Comparative Philosophy
   REGS4356	Comparative Business-Govt Rels
   REGS4973	Principles of Company Law
   REGS5004	Statistical Computation
   REGS5109	Company Law
   REGS5618	Comp Integrated Manufacturing
   REGS7309	Competitive Analysis
   REGS7319	Competitive Marketing Strat.
   REGS7655	Human Rights & Intl Comp Persp
   REGS7726	Composites & Multiphase Polyme
   REGS7908	Service Managing for Comp.Adv.
   REGS7961	Computer Networks & Internets
   REGS8008	Computers in Schools
   REGS8102	Computer Organisation 1
   REGS8126	Client-Server Computing M
   REGS8300	Computers in School Admin
   REGS8488	Company Law
   REGS8546	Comparative Intellectual Prope
   REGS8550	Company Law
   REGS8957	Comparative Law
   REGS9014	Prof Practicum Comp Sci & Eng
   SAFE9122	Computing in Safety Science
   SART1608	Digital Composite 1
   SART1681	Multimedia Computing Elective1
   SART1810	Introduction to Computing
   SART2608	Digital Composite 2
   SART2681	Multimedia Computing Elective2
   SART2811	Multimedia Computing Workshop
   SART2833	Figurative Comp in Painting
   SART2835	Composition and Design
   SART3608	Digital Composite 3
   SART3681	Multimedia Computing Elective3
   SART3840	Advanced Multimedia Computing
   SART9725	Intro to Multimedia Computing
   SART9739	Multimedia Computing Elective
   SART9741	Composition and Design
   SDES1106	Design and Computers 1
   SDES1110	Design and Computers 2
   SDES1111	Integrated Design Computing 1
   SDES1211	Integrated Design Computing 2
   SDES1601	Colour,Composition &Typography
   SDES2107	Design and Computers 3
   SDES2115	Design and Computers 2B
   SDES3107	Design and Computers 4
   SDES4103	Design and Computers 4
   SDES6714	Intro 3D Computer Aided Design
   SLST3211	Computers in Sports Science
   SLST4262	Computer Applications for Rec.
   SLST9896	Computers in Sports Admin.
   SLST9898	Computers in Exercise Science
   SOCA3314	The Messiah Complex
   SOCF5112	Complex Practice Issues
   SOCI3401	Comp Analysis of Social Data A
   SOCI3408	Comp Analysis of Social Data B
   SOCI5310	Survey Sampling & Computer App
   SOCW7801	Managing for Compliance
   SOMA1608	Digital Composite
   SOMA1681	Intro Multimedia Computing
   SOMA1810	Introduction to Computing
   SOMA2402	Tangible Computing
   SOMA2608	Digital Composite 2
   SOMA2681	Advanced Multimedia Computing
   SOMA2811	Multimedia Computing Workshop
   SOMA3415	Compositional Project
   SOMA3608	Digital Composite 3
   SURV1111	Introduction to Computing
   SURV2111	Principles of Comp. Processing
   SURV2122	Computer Graphics 1
   SURV3111	Survey Computations
   SURV3231	Geodetic Computations
   SURV4111	Data Analysis and Computing 1
   SURV5111	Data Analysis and Computing 2
   SURV5122	Computer Graphics 2
   SURV6121	Computer Graphics
   TABL1002	Computer Information Systems
   TABL2053	Acct for Complex Struct & Inst
   TABL2731	Competition and Consumer Law
   TABL3044	Comparative Tax Systems
   TABL5543	Bus Company Law
   TABL5544	Comparative Tax Systems
   TEDG0011	Computers and Teaching 2
   TEDG0022	Computers and Teaching 3
   TEDG1101	Computers in Education
   TEDG1102	Computers and Teaching
   TEDG1103	Computers & the Learning Proc.
   TEDG1104	Issues in Computer Education
   TEDG1106	Comp-Based Res: Design & Prod
   TEDG1107	Managing with Comps in Schools
   TEDG1108	Teach. Curric Courses in Comp
   TEDG1112	Computers - Gifted & Talented
   TEDG1113	Comp Control Tech in Education
   TEDG2022	Computers and Teaching 1
   TEDG2031	Computers in Educational Admin
   TEDG5602	Teach. Curric Courses in Comp
   TEDG5800	Computers and Education 1
   TEDG5801	Computers and Education 2
   TEED1134	Fundamentals of Computing
   TEED2119	Computers and People
   TEED3149	Curric W'shop: Comps in Class
   TEED3173	Comp. Awareness & Media Stud.
   TEED4322	Curric W'shop: Comps in Class
   TELE4343	Source Coding and Compression
   TELE9302	Computer Networks
   TEXT2501	Computing Applications
   WOMS5930	Feminist Analysis & Comp. Apps
   WOMS5950	Managing for Compliance
   YMED3006	Comparative Health Systems
   ZACM3011	Component Design
   ZACM3433	Compressible Flow
   ZACM4020	Computational Structures
   ZACM4031	Compressible Flow
   ZACM4909	Composite Mechanics
   ZACM4913	Eng App of Comp Fluid Dynamics
   ZBUS2200	Markets and Competition
   ZEIT1101	Computational Problem Solving
   ZEIT1110	Computer Games
   ZEIT2102	Computer Technology
   ZEIT2104	Computers and Security
   ZEIT2305	Computer Games
   ZEIT3113	Computer Languages & Algorithm
   ZEIT3304	Computing Proj - Info Sys
   ZEIT3307	Computer Games
   ZEIT4003	Computational Fluid Dynamics
   ZEIT4103	Computer Science 4 (Hons) F/T
   ZEIT7101	Computational Problem Solving
   ZEIT8020	Computer Network Operations
   ZEIT9100	Computer Science Research F/T
   ZEIT9101	Computer Science Research P/T
   ZGEN2300	Computers in Society
   ZGEN2301	Computer Games
   ZHSS8431	Comparative Defence Planning
   ZINT1001	Eng Comp Methods 1
   ZITE1001	Computer Tools for Engineers
   ZITE1101	Intro to Computer Science
   ZITE2101	Computer Languages & Algorithm
   ZITE2102	Computer Technology
   ZITE3101	Computing Proj - Comp Sci
   ZITE3105	Human Computer Interaction
   ZITE3106	Interactive Computer Graphics
   ZITE3113	Computer Languages & Algorithm
   ZITE3211	Microcomputer Interfacing
   ZITE3304	Computing Proj - Info Sys
   ZITE4103	Computer Science 4 (Hons) F/T
   ZITE8104	Computer Security
   ZITE8145	SoftComp
   ZITE9100	Computer Science Research F/T
   ZITE9101	Computer Science Research P/T
   ZPEM3302	Complex Variables
   ```

   The second one looks better because the data itself isn't transformed, only the internal comparisons.

   If we want to know how many courses have "computing" or "computer" in their title, we have to use `grep -E`, which recognises the alternative operator "|", and `wc` to count the number of matches. There are a couple of ways to construct the regexp:

   ```
   grep -E -i 'computer|computing' course_codes.tsv | wc
       372    1632   12808
   ```

   ```
   grep -E -i 'comput(er|ing)' course_codes.tsv | wc
       372    1632   12808
   ```

   If you don't like the irrelevant word and character counts, use `wc -l`.

   Most of these 80 matches were CSE offerings, whose course codes begin with COMP, SENG or BINF. Which of the matches were courses offered by other schools?

   Think about it for a moment.... There's no "but not" regexp operator, so instead we construct a composite filter with an extra step to deal with eliminating the CSE courses:

   ```
   grep -E -i 'computer|computing' course_codes.tsv | grep -E -v '^(COMP|SENG|BINF)'
   ACMA4021	Computer Tools for Eng Mgt
   ACSC1100	Intro to Computer Science
   ACSC1401	Computer Tools for Engineers
   ACSC1501	Computer Tools for Engineers
   ACSC1502	Computer Prog for Engineers
   ACSC1600	Computer Science 1
   ACSC1800	Computer Science 1E
   ACSC2009	Computer Speech Processing
   ACSC2013	Human Computer Interaction
   ACSC2015	Interactive Computer Graphics
   ACSC2101	Computer Science Core 2A
   ACSC2102	Computer Science Core 2B
   ACSC2104	Computer Systems Architecture
   ACSC2106	Computer Languages & Algorithm
   ACSC2107	Computer Languages B
   ACSC2109	Computer Technology
   ACSC2405	Computer Architecture 2EE
   ACSC2601	Computer Science 2A
   ACSC2602	Computer Science 2B
   ACSC2800	Computer Science 2E
   ACSC2801	Computer Science 2CE
   ACSC2802	Computer Science 2EE
   ACSC2803	Computer Science 2AE
   ACSC2804	Computer Science 2ME
   ACSC3003	Computer Project
   ACSC3029	Computing Project 3
   ACSC3034	Human Computer Interaction 3
   ACSC3102	Human Computer Interaction
   ACSC3601	Computer Science 3A
   ACSC3603	Computer Science 3C
   ACSC4191	Computer Science 4 (Hons) F/T
   ACSC4501	Cryptog & Computer Security E
   ACSC4502	Computer Speech E
   ACSC4690	Computer Science 4 (Hon) F/T
   ACSC4691	Computer Science 4 (Hon) P/T
   ACSC7304	Computer Graphics
   ACSC7306	Computer Speech Processing
   ACSC7336	Computer Security
   ACSC7362	Distributed Computing
   ACSC8201	Intro to Computer and Info Sys
   ACSC8211	Computer Graphics
   ACSC8218	Computer Speech Processing
   ACSC8248	Computer Graphics
   ACSC9000	Computer Science Research F/T
   ACSC9001	Computer Science Research P/T
   AELE2007	Computer Design
   AELE2505	Computer Design
   AELE2508	Microcomputer Interfacing
   AELE3015	Computer Design
   AELE3021	Microcomputer Interfacing 1
   AELE3031	Microcomputer Interfacing
   AELE3509	Microcomputer Interfacing
   AELE4005	Microcomputer Interfacing A
   AELE4072	Computer Control Theory
   AELE4511	Computer Control Theory
   ANCE8002	Supercomputing Techniques
   APHY3120	Computers & Electronics in Phy
   ARCH5200	Computer Graphics Programming
   ARCH5201	Computer Applications 1
   ARCH5202	Computer Applications 2
   ARCH5203	Computer Applications 3
   ARCH5205	Theory of Arch Computing
   ARCH5220	Computer Graphics Programming
   ARCH5221	Computer Graphics Programming
   ARCH5222	Computer Applications 1
   ARCH5223	Computer Applications 2
   ARCH5940	Theory of Arch Computing 1
   ARCH5941	Theory of Arch Computing 2
   ARCH5942	Arch Computing Seminar
   ARCH5943	Theory of Arch Computing
   ARCH6201	Architectural Computing 1
   ARCH6205	Architectural Computing 2
   ARCH6214	Architectural Computing 2
   ARCH7204	Design Computing Theory
   ARCH7205	Computer Graphics Programming
   ARCH7221	Computer Modelling & Rendering
   ARTS2301	Computers, Brains & Minds
   ATAX0002	Computer Information Systems
   ATAX0904	Computer Based Acc Spreadsheet
   ATAX0907	Computer Database
   AVEN1500	Computing for Aviation
   BENV1141	Computers and Information Tech
   BENV1242	Computer-Aided Design
   BENV2405	Computer Graphics Programming
   BIOM9501	Computing for Biomedical Eng
   BLDG2281	Introduction to Computing
   BLDG3282	Computer Apps in Building
   BLDG5103	Computers in Management
   BLDG6155	Computers in Construction Mgmt
   CEIC8310	Computing Studies Proc Ind
   CHEM3640	Computers in Chemistry
   CIVL1015	Computing
   CIVL1106	Computing & Graphics
   CODE1231	Urban Computing
   COFA2680	Multi-Media Computing Unit 1
   COFA2681	Multi-Media Computing Unit 2
   COFA2682	Multi-Media Computing Unit 3
   COFA2683	Multi-Media Computing Unit 4
   COFA2684	Multi-Media Computing Unit 5
   COFA3680	M'Media Computing Unit 1(Elec)
   COFA3681	Multimedia Computing Elective1
   COFA3682	Multimedia Computing Elective2
   COFA3810	Introduction to Computing
   COFA3811	Multimedia Computing Workshop
   COFA3840	Advanced Multi-media Computing
   COFA4036	The Computer&the Art Educator
   COFA5116	Design and Computers 1
   COFA5208	Design & Computers:2D & 3D Cad
   COFA5216	Design and Computers 1
   COFA5240	Design and Computers 2 Cad
   COFA5241	Design & Computers 2 Graphics
   COFA5308	Design and Timebased Computer
   COFA5315	Design and Computers 2
   COFA5338	Design and Computers 3 - Cad
   COFA5339	Design&Computers 3 - Graphics
   COFA5434	Design and Computers 4
   COFA6315	Design and Computers S2 Only
   COFA7051	Computer Technology 1
   COFA7052	Computer Technology 2
   COFA8670	Intro to Multimedia Computing
   COFA9058	MAE Elective(Design&Computers)
   CVEN1015	Computing
   CVEN1025	Computing
   DPST1092	Computer Systems Fundamentals
   EDST1492	Computer Skills for Teachers
   EDST2608	Computers & Teaching-Learning
   EDST4092	Computer Skills for Teachers
   EDST4157	Computing Studies Method 1
   EDST4158	Computing Studies Method 2
   ELEC4432	Computer Control &Instrument'n
   ELEC4605	Quantum Devices and Computers
   ELEC4632	Computer Control Systems
   ELEC9401	Computer Control Systems 1
   ELEC9402	Computer Control Systems 2
   ELEC9403	Real Time Computing & Control
   ELEC9733	Real Computing and Control
   ENGG1811	Computing for Engineers
   EXPA2013	Computer Technology 1
   EXPA2014	Computer Technology 2
   EXPA4124	Computer Resources for Artists
   FIBR2201	Computing Applications
   FNDN0301	Computing Studies
   FNDN0302	Computing Studies and Research
   FNDN0303	Computing for Design
   FNDN0304	Computing for Academic Purpose
   FNDN0305	Computing for Acad Purpose H
   FNDN0306	Computing for Acad Purposes S
   FNDN0311	Computing Studies - T
   FNDN0312	Computing Academic Purpose - T
   FNDN0314	Computing for Design - T
   FNDN0315	Computing for Acad Purpose TH
   FNDN0316	Computing for Acad Purp - TS
   FOOD4220	Computer Applications
   FOOD4320	Computer Applications
   FOOD4537	Computing in Food Science
   GEND4201	Design and Computing
   GENE8001	Computer Game Design
   GENM0515	Computers for Professionals
   GENP0515	Computers for Professionals
   GENS2001	The Computer
   GENS5525	Computer: Impact, Signif, Uses
   GENS9038	Mathematics and Computing 1
   GENS9039	Mathematics and Computing 2
   GENS9040	Mathematics and Computing 3
   GENS9041	Mathematics and Computing 4
   GENT0603	Computer: Impact, Signif, Uses
   GENT1003	Computers into the 21st C
   GENZ8501	Computers in Society
   GEOG3071	Computer Cartography
   GEOG3161	Computer Mapping &Data Display
   GEOG3861	Computer Mapping
   GEOG9014	Computer Mapping &Data Display
   GEOG9210	Computer Mapping &Data Display
   GEOL0300	Computing&Stats for Geologists
   GEOL2041	Geological Computing
   GEOL9090	Computing for Groundwater Spec
   GMAT1111	Introduction to Computing
   GMAT2122	Computer Graphics 1
   GMAT3122	Computer Graphics 1
   GMAT4111	Data Analysis and Computing 1
   GMAT4112	Data Analysis and Computing 1
   GMAT5111	Data Analysis and Computing 2
   GMAT5112	Data Analysis and Computing 2
   GMAT5122	Computer Graphics 2
   HDAT9300	Computing 4 HDAT
   HEAL9521	Computer for Postgraduates
   HPSC2610	Computers, Brains & Minds
   HPST2004	Computers, Brains and Minds
   HPST2109	Computers, Brains & Minds
   IDES2121	Introduction to Computing
   IDES3231	Adv Computer Aided Product Des
   IDES5153	Computer Graphic Applications
   IDES5154	Computer Aided Design
   ILAS0233	Computing Applications in the
   INFS1601	Introduction to Computing
   INFS3607	Distributed Computer Systems
   KCME2104	Appl'n of Computers in Mining
   LAND1131	Intro to Computer Applications
   LAWS1032	Computer Applications to Law
   LAWS4609	Develop Computer Apps to Law
   LAWS4620	Computer Applications to Law
   MANF3500	Computers in Manufacturing 1
   MANF4500	Computers in Manufacturing 2
   MANF8560	Computer Integrated Manufact.
   MANF9460	Computer Integrated Manufact.
   MANF9500	Computer-Aided Progrmg for Num
   MANF9520	Computer-Aided Manufacture
   MANF9560	Computer Integrated Manufact.
   MARK3022	Computer Applications in Mktg
   MATH1061	Introductory Applied Computing
   MATH2301	Mathematical Computing
   MATH2430	Symbolic Computing
   MATH2810	Statistical Computing
   MATH2910	Higher Statistical Computing
   MATH3301	Advanced Math Computing
   MATH3430	Symbolic Computing
   MATH3821	Stat Modelling & Computing
   MATH5315	High Perf Numerical Computing
   MATH9315	Math Computing(H Perf Num Com)
   MATS1021	Computing in Materials Science
   MECH1500	Computing 1M
   MECH3500	Computing 2M
   MECH3510	Computing Applications in Mech
   MECH3530	Computing Applcts in Mech.Sys.
   MECH4130	Computer-Aided Eng Design
   MECH4500	Computing 3M
   MECH4509	Computing Science for Mech Eng
   MECH9130	Computer-Aided Eng Design
   MEFT5103	Computer Media
   MINE0710	Computing 1
   MINE1720	Microcomputers (Mining)
   MINE1730	Computer Application in Mining
   MNGT0533	Special Topics in Computing
   MTRN3530	Computing Applcts in Mech.Sys.
   PHIL5206	AI & Computer Science
   PHIL5207	AI and Computer Science 2A
   PHYS2601	Computer Applications 2
   PLAN1061	Computer Literacy
   PLAN2413	Computers&Information Systems
   PLAN2414	Computer Applicat'n in Plan 1
   PSYC3191	Computer Science & Psychology
   PTRL1013	Computing-Petroleum Engineers
   REGS0010	Numerical and Computer Methods
   REGS3410	Computer Networks
   REGS3561	Computers in Business
   REGS3732	Adv Computerised Legal Res
   REGS3765	Computerized Legal Inf Systems
   REGS3835	Computer Law
   REGS3874	Computer Based Info Systems
   REGS7961	Computer Networks & Internets
   REGS8008	Computers in Schools
   REGS8102	Computer Organisation 1
   REGS8126	Client-Server Computing M
   REGS8300	Computers in School Admin
   SAFE9122	Computing in Safety Science
   SART1681	Multimedia Computing Elective1
   SART1810	Introduction to Computing
   SART2681	Multimedia Computing Elective2
   SART2811	Multimedia Computing Workshop
   SART3681	Multimedia Computing Elective3
   SART3840	Advanced Multimedia Computing
   SART9725	Intro to Multimedia Computing
   SART9739	Multimedia Computing Elective
   SDES1106	Design and Computers 1
   SDES1110	Design and Computers 2
   SDES1111	Integrated Design Computing 1
   SDES1211	Integrated Design Computing 2
   SDES2107	Design and Computers 3
   SDES2115	Design and Computers 2B
   SDES3107	Design and Computers 4
   SDES4103	Design and Computers 4
   SDES6714	Intro 3D Computer Aided Design
   SLST3211	Computers in Sports Science
   SLST4262	Computer Applications for Rec.
   SLST9896	Computers in Sports Admin.
   SLST9898	Computers in Exercise Science
   SOCI5310	Survey Sampling & Computer App
   SOMA1681	Intro Multimedia Computing
   SOMA1810	Introduction to Computing
   SOMA2402	Tangible Computing
   SOMA2681	Advanced Multimedia Computing
   SOMA2811	Multimedia Computing Workshop
   SURV1111	Introduction to Computing
   SURV2122	Computer Graphics 1
   SURV4111	Data Analysis and Computing 1
   SURV5111	Data Analysis and Computing 2
   SURV5122	Computer Graphics 2
   SURV6121	Computer Graphics
   TABL1002	Computer Information Systems
   TEDG0011	Computers and Teaching 2
   TEDG0022	Computers and Teaching 3
   TEDG1101	Computers in Education
   TEDG1102	Computers and Teaching
   TEDG1103	Computers & the Learning Proc.
   TEDG1104	Issues in Computer Education
   TEDG1112	Computers - Gifted & Talented
   TEDG2022	Computers and Teaching 1
   TEDG2031	Computers in Educational Admin
   TEDG5800	Computers and Education 1
   TEDG5801	Computers and Education 2
   TEED1134	Fundamentals of Computing
   TEED2119	Computers and People
   TELE9302	Computer Networks
   TEXT2501	Computing Applications
   ZEIT1110	Computer Games
   ZEIT2102	Computer Technology
   ZEIT2104	Computers and Security
   ZEIT2305	Computer Games
   ZEIT3113	Computer Languages & Algorithm
   ZEIT3304	Computing Proj - Info Sys
   ZEIT3307	Computer Games
   ZEIT4103	Computer Science 4 (Hons) F/T
   ZEIT8020	Computer Network Operations
   ZEIT9100	Computer Science Research F/T
   ZEIT9101	Computer Science Research P/T
   ZGEN2300	Computers in Society
   ZGEN2301	Computer Games
   ZITE1001	Computer Tools for Engineers
   ZITE1101	Intro to Computer Science
   ZITE2101	Computer Languages & Algorithm
   ZITE2102	Computer Technology
   ZITE3101	Computing Proj - Comp Sci
   ZITE3105	Human Computer Interaction
   ZITE3106	Interactive Computer Graphics
   ZITE3113	Computer Languages & Algorithm
   ZITE3211	Microcomputer Interfacing
   ZITE3304	Computing Proj - Info Sys
   ZITE4103	Computer Science 4 (Hons) F/T
   ZITE8104	Computer Security
   ZITE9100	Computer Science Research F/T
   ZITE9101	Computer Science Research P/T
   ```

   The last ones are from the Computer Science school at ADFA.

2. Consider a file called [enrollments.txt](/enrollments.txt) which contains data about student enrollment in courses. There is one line for each student enrolled in a course:

   ```
   ls -l enrollments.txt
   -rw-r--r-- 1 cs2041 cs2041 671546 May 29 09:57 enrollments.txt
   ```

   ```
   wc enrollments.txt
     9602  24342 671546 enrollments.txt
   ```

   ```
   head enrollments.txt
   COMP1911|5200805|Lim, Zheng|3409/1|MTRNAH|055.000|22T2|19940511|M
   COMP4952|5243213|West, Ke|4515/1|COMPI1 MATHC2|067.150|22T2|20000918|M
   COMP1511|5285558|Ho, Zekun|3778/1|PSYCA1|072.500|22T2|20031104|M
   COMP9511|5242183|Zhang, Yang|3778/3|COMPA1 FINSA1|061.333|22T2|20020903|F
   COMP1911|5212243|Wu, Karen|3707/4|REGZF1|068.462|22T2|19990930|F
   COMP9902|5285248|Phan, Jennifer Ana|3785/3|COMPCS|065.038|22T2|19970810|F
   COMP9024|5205794|Ruan, Zain|3707/1|COMPA1|079.667|22T2|20040730|M
   COMP2041|5206380|Huynh, Zhibo|3778/3|COMPAS COMPSS|067.000|22T2|20060513|M
   COMP3141|5206380|Huynh, Zhibo|3778/3|COMPAS COMPSS|067.000|22T2|20060513|M
   COMP2041|5217801|Tang, Harry|3778/3|COMPI1 FINSA1|076.400|22T2|20060205|M
   ```

   The following commands count how many students are enrolled in COMP2041 or COMP9041. The course IDs differ only in one character, so a character class is used instead of alternation.

   The first version below is often ferred because initially you may want to know "*how many xxx*", then having found that out the next question might be, "*well give me a sample of 10 or so of them*". Then it's a simple matter of replacing `wc` by `head`.

   ```
   grep -E '^COMP(2041|9044)' enrollments.txt | wc -l
   790
   ```

   ```
   grep -E -c '^COMP(2041|9044)' enrollments.txt
   790
   ```

   The last field field in the [enrollment](/enrollments.txt) file records the student's gender. This command counts the number of female students enrolled in the courses.

   ```
   grep -E '^COMP(2041|9044)' enrollments.txt | grep -E 'F$' | wc -l
   189
   ```

   Not a very good gender balance, is it?

   By the way, the two `grep -E`s could have been combined into one. How?

   This command will give a sorted list of course codes:

   ```
   cut -d'|' -f1 enrollments.txt | sort | uniq
   COMP1010
   COMP1511
   COMP1521
   COMP1531
   COMP1911
   COMP2041
   COMP2511
   COMP2521
   COMP3121
   COMP3141
   COMP3151
   COMP3153
   COMP3331
   COMP3511
   COMP3900
   COMP3901
   COMP4336
   COMP4601
   COMP4951
   COMP4952
   COMP4953
   COMP4961
   COMP4962
   COMP4963
   COMP6443
   COMP6447
   COMP6452
   COMP6721
   COMP6741
   COMP6771
   COMP6843
   COMP9020
   COMP9021
   COMP9024
   COMP9044
   COMP9101
   COMP9153
   COMP9154
   COMP9242
   COMP9311
   COMP9312
   COMP9313
   COMP9319
   COMP9323
   COMP9331
   COMP9336
   COMP9414
   COMP9417
   COMP9444
   COMP9447
   COMP9491
   COMP9511
   COMP9517
   COMP9727
   COMP9900
   COMP9901
   COMP9902
   COMP9991
   COMP9992
   COMP9993
   ```

   The student records system known to users as myUNSW is built on top of a large US product known as PeopleSoft (the company was taken over by Oracle in 2004). On a scale of 1 to 10 the quality of the design of this product is about 3. One of its many flaws is its insistence that everybody must have two names, a "Last Name" and a "First Name", neither of which can be empty. To signify that a person has only a single name (common in Sri Lanka, for example), the system stores a dot character in the "First Name" field. The enrollments file shows the data as stored in the system, with a comma and space separating the component names. It has some single-named people (note that the names themselves have been disguised):

   ```
   grep -E ', \.' enrollments.txt
   COMP1531|5242480|Zheng, .|3784/2|SENGAH|064.200|22T2|19981022|F
   COMP3121|5242480|Zheng, .|3784/2|SENGAH|064.200|22T2|19981022|F
   COMP1511|5270958|Chung, .|3778/3|COMPA1|056.000|22T2|19980124|M
   COMP2041|5269622|Lee, .|3785/1|COMPA1|066.682|22T2|19901107|F
   COMP3900|5228820|Lei, .|8543|COMPA1 IBUSA1|068.214|22T2|19970122|F
   COMP9313|5214813|Ding, .|1120|COMPCS|066.933|22T2|20000828|F
   COMP9323|5214813|Ding, .|1120|COMPCS|066.933|22T2|20000828|F
   COMP2521|5271997|Ahuja, .|3778/1|COMPA1|063.167|22T2|19991115|M
   COMP9444|5231435|Kha, .|3707/1|COMPA1|071.960|22T2|20001223|M
   COMP1511|5235854|Shah, .|8543|COMPAS COMPSS|078.478|22T2|19850915|F
   COMP2521|5220687|Cheng, .|3781/2|COMPBH|077.136|22T2|20001014|F
   COMP9021|5213052|Nie, .|3707/3|COMPA1|073.385|22T2|20021122|M
   COMP9024|5213052|Nie, .|3707/3|COMPA1|073.385|22T2|20021122|M
   COMP4951|5293922|Hou, .|3778/2|MATHTS|073.800|22T2|20030519|F
   COMP9331|5256052|Xin, .|8543|COMPY1|065.000|22T2|19940530|M
   COMP3900|5297142|Xiao, .|3784/3|COMPCS|065.250|22T2|20020326|F
   COMP2041|5284862|Yao, .|3707/1|SENGAH|080.400|22T2|20000714|F
   COMP1531|5267902|Cao, .|3778/2|COMPA1|061.800|22T2|19951114|F
   COMP2511|5270249|Pu, .|8543|COMPA1|066.462|22T2|19991010|M
   COMP3141|5270249|Pu, .|8543|COMPA1|066.462|22T2|19991010|M
   COMP1531|5237103|Yeh, .|3961/1|COMPA1|080.833|22T2|19990407|M
   COMP9414|5217161|Su, .|3761/1|FINSA1 INFSA1|084.308|22T2|20010906|M
   COMP3141|5262984|Bell, .|8543|COMPA1|056.333|22T2|19960725|M
   COMP1511|5267375|Kim, .|3784/2|COMPSS|080.185|22T2|20000304|M
   COMP1521|5226310|Long, .|3778/3|COMPA1|062.353|22T2|20070615|M
   COMP2041|5217827|Wu, .|4787/5|COMPES|073.714|22T2|20001030|M
   COMP2521|5217827|Wu, .|4787/5|COMPES|073.714|22T2|20001030|M
   COMP6443|5217827|Wu, .|4787/5|COMPES|073.714|22T2|20001030|M
   COMP2041|5258228|Jing, .|3784/4|COMPA1|075.786|22T2|20040503|F
   COMP3511|5212009|Ni, .|3778/1|AEROAH|070.833|22T2|20090429|M
   COMP4952|5212009|Ni, .|3778/1|AEROAH|070.833|22T2|20090429|M
   COMP9313|5212009|Ni, .|3778/1|AEROAH|070.833|22T2|20090429|M
   COMP9511|5285881|Deng, .|3781/3|COMPY1|084.167|22T2|20050321|M
   COMP3141|5296083|Tran, .|3762/3|COMPAS|071.000|22T2|20000830|F
   COMP6443|5296083|Tran, .|3762/3|COMPAS|071.000|22T2|20000830|F
   COMP9319|5264194|Qin, .|3778/1|COMPA1|048.474|22T2|19980122|M
   COMP9491|5244457|Han, .|3784/2|COMPAS|077.700|22T2|20010118|M
   COMP9900|5244457|Han, .|3784/2|COMPAS|077.700|22T2|20010118|M
   COMP3121|5294606|Luo, .|8543|COMPCS|046.167|22T2|19900717|M
   COMP3141|5294606|Luo, .|8543|COMPCS|046.167|22T2|19900717|M
   COMP6771|5294606|Luo, .|8543|COMPCS|046.167|22T2|19900717|M
   COMP9444|5225331|Zhou, .|3778/3|COMPA1 LAWSA1|084.547|22T2|20011208|F
   COMP2511|5235450|Luo, .|3782/1|COMPA1|071.692|22T2|19970619|F
   COMP9020|5281867|Chow, .|3784/1|COMPSS|075.667|22T2|20020706|M
   COMP9021|5281867|Chow, .|3784/1|COMPSS|075.667|22T2|20020706|M
   COMP9311|5281867|Chow, .|3784/1|COMPSS|075.667|22T2|20020706|M
   COMP9414|5211550|Lu, .|8543|COMPCS|056.818|22T2|20010311|F
   COMP9417|5211550|Lu, .|8543|COMPCS|056.818|22T2|20010311|F
   COMP9517|5211550|Lu, .|8543|COMPCS|056.818|22T2|20010311|F
   COMP4953|5219604|Gao, .|3785/5|COMPA1|085.600|22T2|19960726|F
   COMP6443|5219604|Gao, .|3785/5|COMPA1|085.600|22T2|19960726|F
   COMP9024|5224010|Qi, .|8543|BINFAH|072.500|22T2|19961215|M
   COMP9331|5224010|Qi, .|8543|BINFAH|072.500|22T2|19961215|M
   COMP9414|5224010|Qi, .|8543|BINFAH|072.500|22T2|19961215|M
   COMP2511|5295456|Huang, .|3783/1|FINSA1|067.800|22T2|19950818|M
   COMP1531|5225951|Lee, .|8543|COMPA1|022.200|22T2|19970217|F
   COMP2521|5225951|Lee, .|8543|COMPA1|022.200|22T2|19970217|F
   COMP9044|5267209|Su, .|3778/3|COMPA1|069.714|22T2|20021221|M
   COMP9414|5267209|Su, .|3778/3|COMPA1|069.714|22T2|20021221|M
   COMP9517|5267209|Su, .|3778/3|COMPA1|069.714|22T2|20021221|M
   COMP9331|5245370|Tsai, .|3764/4|COMPA1 MATHU1|046.000|22T2|20020813|M
   COMP3141|5214527|Lim, .|3768/5|COMPA1|059.292|22T2|19990423|F
   COMP4952|5214527|Lim, .|3768/5|COMPA1|059.292|22T2|19990423|F
   COMP9101|5273105|He, .|8543|SENGAH|085.643|22T2|19960609|M
   COMP9311|5273105|He, .|8543|SENGAH|085.643|22T2|19960609|M
   COMP9414|5273105|He, .|8543|SENGAH|085.643|22T2|19960609|M
   ```

   What would have happened if we forgot the backslash?

   If we wanted to know how many different students there were of this type rather than all enrollments, just cut out the second field (student ID) and use `uniq`. It's not necessary to sort the data in this case only because the data is ***clustered,*** that is, all equal values are adjacent although they're not necessarily sorted.

   ```
   grep -E ', \.' enrollments.txt | cut -d'|' -f2 | uniq | wc
        41      41     328
   ```

3. Now let us turn our attention from students and courses to programs. The enrollments file, as well as linking a student to the courses they're taking, also links them to the program (degree) that they are currently enrolled in. Consider that we want to find out the program codes of the students taking COMP2041. The following pipeline will do this:

   ```
   grep -E 'CCOMP(2041|9044)' enrollments.txt | cut -d'|' -f4 | cut -d/ -f1  | sort | uniq
   ```

   If we want to know how many students come from each program, ordered from most common program to least common program, try this:

   ```
   grep -E 'COMP(2041|9044)' enrollments.txt | cut -d'|' -f4 | cut -d/ -f1 | sort | uniq -c | sort -nr
       229 8543
       152 3778
        87 3707
        58 3784
        47 3785
        21 3959
        21 3789
        18 3764
        14 3674
        13 1650
        12 4515
        11 3791
        11 3782
        11 3781
        11 3768
         8 3673
         6 8338
         6 3783
         5 3970
         5 3738
         5 3706
         4 3761
         3 7543
         3 3767
         3 3736
         2 3961
         2 3956
         2 3762
         2 3734
         1 8959
         1 7959
         1 5543
         1 5341
         1 4787
         1 4770
         1 3979
         1 3978
         1 3786
         1 3765
         1 3632
         1 3521
         1 3387
         1 3268
         1 3155
         1 3132
         1 3131
         1 2645
   ```

   Note that a tab is usually inserted between the count and the data, but not all implementations of the `uniq` command ensure this.

4. Consider a file called [program_codes.tsv](https://cgi.cse.unsw.edu.au/~cs2041/23T2//topic/filters/data//program_codes.tsv) that contains the code and name of each program offered at UNSW (excluding research programs):

   ```
   wc program_codes.tsv
    250 1001 7295 program_codes.tsv
   ```

   ```
   head program_codes.tsv
   1004 	Joint PhD
   1292 	PhD Art, Design and Media
   1400 	Psychology
   1540 	Economics
   1545 	Actuarial Studies
   1550 	Marketing
   1561 	Banking and Finance
   1630 	Civil & Environmental Eng
   1640 	Electrical Engineering
   1650 	Computer Science and Eng
   ```

   We can use this file to give more details of the programs that COMP2041 students are taking, if some users don't want to deal with just course codes.

   ```
   grep -E 'COMP(2041|9044)' enrollments.txt | cut -d'|' -f4 | cut -d/ -f1 | sort | uniq | join - program_codes.tsv
   1650 Computer Science and Eng
   2645 Engineering (MPhil)
   3131 Mat Sci and Eng Hons
   3132 Mat Sci and Eng Hons/Eng Sci
   3155 Actuarial Studies / Commerce
   3268 Computational Design
   3387 Industrial Design
   3521 Commerce/Economics
   3632 Advanced Science (Honours)
   3673 Economics / Computer Science
   3674 Actuarial Stu / Computer Sci
   3706 Engineering Science
   3707 Engineering (Honours)
   3734 Engineering Science / Commerce
   3736 BE (Hons) ME Elec Eng
   3738 Engineering Science / CompSc
   3761 Adv Math (Hons) / Eng (Hons)
   3762 AdvSci(Hons)/Engineering(Hons)
   3764 Engineering (Hons)/Commerce
   3765 Engineering (Honours) / Law
   3767 Engineering (Hons) / Science
   3768 Eng (Hons) / MBiomedE
   3778 Computer Science
   3781 Adv Maths (Hons) / Comp Sci
   3782 Adv Science (Hons) / Comp Sci
   3783 Computer Science / Arts
   3784 Commerce / Computer Science
   3785 Engineering (Hons) / Comp Sci
   3786 Computer Science / Law
   3789 Science / Computer Science
   3791 Computer Science / Media Arts
   3956 Advanced Mathematics (Honours)
   3959 Data Science and Decisions
   3961 Engineering (Honours) / Arts
   3970 Science
   3978 Computer Science
   3979 Information Systems
   4515 Comp Sci & Eng (Honours)
   4770 Science / Law
   5341 Engineering Science
   5543 Information Technology
   7543 Computing
   8338 Engineering Science
   8543 Information Technology
   8959 Data Science and Decisions
   ```

   We can combine the enrollment counts (for both courses) with the program titles to produce a self-descriptive tally. It's even better if it's in decreasing order of popularity, so after joining the tallies with the program titles, re-sort the composite data:

   ```
   grep -E 'COMP(2041|9044)' enrollments.txt | cut -d'|' -f4 | cut -d/ -f1 | sort | uniq -c | join -1 2 -a 1 - program_codes.tsv  | sort -k2rn
   8543 229 Information Technology
   3778 152 Computer Science
   3707 87 Engineering (Honours)
   3784 58 Commerce / Computer Science
   3785 47 Engineering (Hons) / Comp Sci
   3789 21 Science / Computer Science
   3959 21 Data Science and Decisions
   3764 18 Engineering (Hons)/Commerce
   3674 14 Actuarial Stu / Computer Sci
   1650 13 Computer Science and Eng
   4515 12 Comp Sci & Eng (Honours)
   3768 11 Eng (Hons) / MBiomedE
   3781 11 Adv Maths (Hons) / Comp Sci
   3782 11 Adv Science (Hons) / Comp Sci
   3791 11 Computer Science / Media Arts
   3673 8 Economics / Computer Science
   3783 6 Computer Science / Arts
   8338 6 Engineering Science
   3706 5 Engineering Science
   3738 5 Engineering Science / CompSc
   3970 5 Science
   3761 4 Adv Math (Hons) / Eng (Hons)
   3736 3 BE (Hons) ME Elec Eng
   3767 3 Engineering (Hons) / Science
   7543 3 Computing
   3734 2 Engineering Science / Commerce
   3762 2 AdvSci(Hons)/Engineering(Hons)
   3956 2 Advanced Mathematics (Honours)
   3961 2 Engineering (Honours) / Arts
   2645 1 Engineering (MPhil)
   3131 1 Mat Sci and Eng Hons
   3132 1 Mat Sci and Eng Hons/Eng Sci
   3155 1 Actuarial Studies / Commerce
   3268 1 Computational Design
   3387 1 Industrial Design
   3521 1 Commerce/Economics
   3632 1 Advanced Science (Honours)
   3765 1 Engineering (Honours) / Law
   3786 1 Computer Science / Law
   3978 1 Computer Science
   3979 1 Information Systems
   4770 1 Science / Law
   4787 1
   5341 1 Engineering Science
   5543 1 Information Technology
   7959 1
   8959 1 Data Science and Decisions
   ```

   Note the curious extra space before the title of some programs. It took me a while to work it out, can you? (Hint: how are the programs shown in the enrollment file?) Suggest an appopriate change to the pipeline.

5. Lecture exercises on `wc`:

   1. how many different programs does UNSW offer?

      ```
      wc -l program_codes.tsv
      250 program_codes.tsv
      ```

   2. how many times was WebCMS accessed?

      ```
      wc -l access_log.txt
      59779 access_log.txt
      ```

   3. how many students are studying in CSE?

      ```
      wc -l enrollments.txt
      9602 enrollments.txt
      ```

      The above solutions assume that we're talking about total enrollments. If the question actually meant how many distinct indivduals are studying courses offered by CSE, then we'd answer it as:

      ```
      cut -d'|' -f2 enrollments.txt | sort | uniq | wc -l
      6219
      ```

   4. how many words are there in the [book](/book.txt)

      ```
      wc -w book.txt
      60428 book.txt
      ```

   5. how many lines are there in the [story](/story.txt)

      ```
      wc -l story.txt
      87 story.txt
      ```