# Robolurn Documentation

Name to be determined

## Usage

Sometimes if things are acting strangely, open the right side menu (with the
arrow) and hit "Clear". Here are some example commands; they can be ran
separately or all at once.

``` 
visit[0,-2];
pick all;
visit [4,-4];
pick all;
visit[4,3];
pick all;
visit[-3,3];
pick all;
drop all has color red;
visit[-3,2];
drop all has color green;
visit[-3,1];
drop all;
visit [0,0]
```


## Important Files

- `actions/world.js` - holds methods dealing with dispatching changes to the
world and communicating with SEMPRE 
- `constants/strings.js` - holds configuration strings such as the URL of the
SEMPRE server
- `helper/blocks.js` - holds helper methods for mutating the arrangement of the
blocks and robot in the visual world
- `routes/Build/index.js` - holds the method activating the rendering of the
screen displaying the block world
- `setting/BlocksWorld/index.js` - holds methods for the actual visual rendering
of the block world
- `store/world.js` - holds Redux reducer (mutator) for the state of world; also
holds the initial state of the world.
