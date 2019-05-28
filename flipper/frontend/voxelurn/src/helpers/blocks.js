import { worldAngle } from "constants/world"

const zScale = -Math.atan(1/Math.sqrt(2));
const yScale = Math.cos(Math.PI/4 - worldAngle);
const xScale = Math.cos(Math.PI/4 + worldAngle);

export function sortBlocks(blocks) {
  return blocks.sort((a, b) => {
    let aNear = a.x*xScale + a.y*yScale + a.z*zScale;
    let bNear = b.x*xScale + b.y*yScale + b.z*zScale;

    if (aNear > bNear)
      return -1;
    else if (aNear < bNear)
      return 1;

    return 0;
  });
}

export function adjustRobot(r, b) {
  // r for robot, b for blocks
  let swap;
  let robotIndex = -1;
  for (let i = 0; i < b.length; ++i) {
    if (b[i].type === "robot") {
      robotIndex = i;
    } else if (robotIndex === -1) {
      continue;
    } else if ((b[i].x - r.x) > -0.5
        && (b[i].y - r.y) > -0.5
        && b[i].z < 4) {
      swap = b[i];
      b[i] = b[robotIndex];
      b[robotIndex] = swap;
      robotIndex = i;
    } /*else if ((b[i-1].type === "robot" && (b[i].type === "item" || b[i].type === "marker"))
        || (b[i-1].type === "marker" && (b[i].type === "item"))) {
      swap = b[i-1];
      b[i-1] = b[i];
      b[i] = swap;
    }
    */
     
  }
}

export function rotateBlock (b, rotational, width = 1) {
	let x = b.x;
	let y = b.y;
	switch (rotational) {
		case -1:
			x = b.x;
			y = b.y;
			break;
		case -2:
			x = b.y;
			y = width - 1 - b.x;
			break;
		case 1:
			x = width - 1 - b.y;
			y = b.x;
			break;
		case 2:
			x = width - 1 - b.x;
			y = width - 1 - b.y;
			break;
		default:
	}
	return { ...b, x: x, y: y };
}

  // Might need to adapt this for carried items as well
  export function resolveZ(x, y, blocks) {
    const filtered = [];
    for (let i = 0; i < blocks.length; ++i) {
      if (blocks[i].type === "item" && blocks[i].x === x && blocks[i].y === y) {
        filtered.push(blocks[i]);
        blocks.splice(i, 1);
        --i;
      }
    }
    const sorted = filtered.sort((a,b) => {return a.z > b.z});
    for (let i = 0; i < sorted.length; ++i) {
      sorted[i].z = i;
    }
    blocks.push.apply(blocks, sorted);
  }

  export function pickItem(x, y, color, shape, blocks, robot) {
    for (let i = 0; i < blocks.length; ++i) {
      if (blocks[i].x === x && blocks[i].y === y && blocks[i].color === color && blocks[i].shape === shape) {
        blocks.splice(i, 1);
        --i;
        robot.items.push([color, shape]);
        resolveZ(x, y, blocks);
        return true;
      }
    }
    return false;
  }

  export function dropItem(x, y, color, shape, blocks, robot) {
	  
	  var index = -1;
	  for (var i = 0; i < robot.items.length; ++i){
		  if (robot.items[i][0] === color && robot.items[i][1] === shape){
			  index = i;
			  break;
		  }
	  }
    if (index != -1) {
      robot.items.splice(index, 1);
      // z value does not mean anything, it is just very high so it is on top of the stack
      blocks.push({x:x, y:y, z:0xffff, type:"item", color:color, shape:shape});
      resolveZ(x, y, blocks);
      return true;
    }
    return false;
  }

  export function removeRobot(blocks) {
    for (let i = 0; i < blocks.length; ++i) {
      if (blocks[i].type === "robot"
          || blocks[i].type === "carriedItem") {
        blocks.splice(i, 1);
        --i;
      }
    }
  }

  // Maybe it would be better to move the robot instead of recreating it?
  export function updateRobot(blocks, robot, step, path, factor) {
	  
    const c = Math.ceil(1.0*step/factor);
    const f = Math.floor(1.0*step/factor);
    if (typeof path === "undefined") {
      // Should something be here?
    } else {
      if (path[c] && path[c].action === "pickitem" && !path[c].completed) {
        pickItem(path[c].x, path[c].y, path[c].color, path[c].shape, blocks, robot);
        path[c].completed = true;
      } else if (path[c] && path[c].action === "dropitem" && !path[c].completed) {
        dropItem(path[c].x, path[c].y, path[c].color, path[c].shape, blocks, robot);
        path[c].completed = true;
      } else if (path[f] && path[c]) {
        const d = 1.0*step/factor - f;
        robot.x = ((1-d)*path[f].x + (d)*path[c].x);
        robot.y = ((1-d)*path[f].y + (d)*path[c].y);
      } else if (path[step]) {
        robot.x = path[step].x;
        robot.y = path[step].y;
      }
    }

    blocks.push(robot);
    for (let i = 0; i < robot.items.length; ++i) {
      // 4 is the height of the robot
      blocks.push({
        x: robot.x, y: robot.y, z:(4+i),
        color: robot.items[i][0],
        shape: robot.items[i][1],
        type: "carriedItem"
      });
    }
    return blocks;
  }
