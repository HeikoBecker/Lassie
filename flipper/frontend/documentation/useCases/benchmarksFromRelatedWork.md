# Benchmarks from existing work

In short, the most common evaluation methods are
 - giving the system to testers and letting them do as they wish with it (later testing how well the system reacted)
 - creating some kind of game/competition
 - showing a task (e.g. in a video) and asking testers to describe it as instructions (then using these utterances for further testing)
 - giving a concrete task that needs to be accomplished using the system

---------------

In this document the experimental setup from all related work is enumerated (for the future comparison).

1. Learning Environmental Knowledge from Task-Based Human-Robot Dialog (Kollar and others)
 - setup: robot accepts natural language commands and may ask clarification questions. The task is fixed (navigation)
 - 9 different people were asked to  give a robot commands to go to destinations in a real-world environment (free language commands, six locations that were known to robots by their code - room number - and to humans by the code and other expressions). Success is measured by number of questions robot had to ask to get to understand the utterance completely
<br /><br />
2. Learning to Interpret Natural Language Commands through Human-Robot Dialog (Thomason and others)
 - setup: robot accepts natural language commands and may ask clarification questions. The task is fixed (navigation and delivery)
 - navigation to one of 10 possible goals (split: 8 for training, 2 for testing)
 - delivery goals with 50 options: 10 locations x 5 items (split: 40 for training, 10 for testing)
 - success measure: users were filling out the survey on their satisfaction with the system; number of questions robot had to ask was measured (its decrease is a sign of success)
 - the tests were performed with Amazon Mechanical Turk (AMT) users (simulation) and with group of students (real robots)
<br /><br />
3. Naturalizing a Programming Language via Interactive Learning (Wang and others)
 - setup: system can build shapes out of voxels of different colors. It accepts natural language utterance, but there is an assumption that users know the underlying core (formal) language. If the utterance is not understood, user is asked to rephrase it (giving the explanation in the core language or simplifying the utterance). One utterance can be explained by sequence of core commands/simpler utterances (*step by step explanation*). The final goal is that the knowledge of the core language is not needed for the users that join late.
  - AMT users were asked to reproduce exactly a shown structure (thus qualifying for the participation) and were then given 30 minutes to build whatever structure they liked.
  - the success measure is how much of naturalization is happening (the ratio of induced utterances and the ones from the core language)
  - the Turkers were incentivized by daily prizes for different categories (bridge, house, animal...). The prizes were awarded for the citations too (with the idea to provoke users to define reusable utterances)
<br /><br />
4. Provably Correct Reactive Control from Natural Language (Lignos and others)
 - setup: a fixed set of supported commands is offered. They are mapped to VerbNet senses (so that the meaning can be restored even if the user uses different utterances that the foreseen ones). The commands are translated to LTL formulas (so the translation must include identification of conditionals, negations, quantification, boolean connections...). A robot is also able to answer a question such as *What are you doing?* (structure that maps LTL tree to the utterance tree)
 - the system was tested by including it into a first-person 3D video game where the participants played a role of a human that used a robot-helper for search 14 rooms, dismantle bombs (robot) and rescue hostages (human). The control over robot was given only by natural language communication.
 - the measure of success was how many valid commands were understood (valid commands = the one that talks about visiting a room or dismantling a bomb). The result is 94% correctly understood commands.
 <br /><br />
5. Improved Semantic Parsers for If-Then Statements (Quirk and Beltagy)
 - setup: the system tries to translate *If-Then* utterances to simple programs (recipes). It uses data from ifttt.com, containing ~100000 description-recipe pairs. Since the descriptions are only mildly connected to recipes (their goal is different), they can't use semantic parsing. Therefore, the neural net approach is emplyed.
 - evaluation is done by providing description unseen during the training phase and expecting the recipe as an output. They reach the accuracy of 42.5%
<br /><br />
6. Understanding Natural Language Commands for Robotic Navigation and Mobile Manipulation (Tellex and others)
 - setup: the robot forklift that picks up pallets and moves them through environment.
 - evaluation: first, a set of videos with robot performing actions was given to Amazon Mechanical Turk users (Turkers). They provided natural language description of those videos. The descriptions were later manually annotated (to match the structure SDC for describing the scene) (that was the initial training set). Negative examples were provided by randomly associating an SDC to an utterance (and checked manually)
 - after training, the evaluation happened on the held-out set and reached accuracy of 86% (F-score: 89%). This evaluation took only into account SDC annotations.
 - end to end evaluation: robot performed the action based on the utterance provided. Turkers would then watch the video and grade how much is robot action in agreement with description provided. For top 30 commands (highest posterior probability of the final plan) they reach the precision of 54% (for the random cost function - not learned - the precision is 28%).
 <br /><br />
7. A model for Verifieable Grounding and Execution of Complex Natural Language Instructions (Boteanu and others)
 - setup: the question is how to perform grounding (based on previous work with DCG) but in the context of changing environment.
 - the train set was obtained by recording videos and then asking users to describe the videos in natural language (50 responses). Groundings were further annotated manually for DCG annotations (the role of each word in the utterance)
 - no measure of system performance is given
 <br /><br />
8. Program Synthesis from Natural Language Using Recurrent Neural Networks (Xi Victoria Lin and others)
 - setup: a user wants to implement a simple bash script, but doesn't know how. Thte Tellina system learns from task description - bash script commands how to do it. It does it using "data types (dates, regexes etc)" to decide on which template to use and then which arguments to provide to the template.
 - the evaluation is provided for top-k-full-command accuracy (success if the one of top k ranked commands semantically matches the description) (k=3, 36%) and top-k-template accuracy (k=3, 80%).
 - the results are not perfect, but a user study was conducted to show that even if the system can't translate natural language to the correct bash script, its guess can still help developer more than searching over SO or Google. 39 students were recruited and given up to 8 tasks. The results indicated that programmers using Tellina were much faster
 - the participants were also given a survey about satisfaction using Tellina
