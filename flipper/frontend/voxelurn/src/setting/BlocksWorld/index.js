import React from "react"
import Isomer,
{
  Point,
  Shape,
  Color,
  Path
} from "isomer";
import {
  sortBlocks,
  adjustRobot,
  rotateBlock,
  removeRobot,
  resolveZ,
  updateRobot
} from "helpers/blocks"
import deepEqual from "deep-equal"
import cssColors from "color-name"

import { worldConfig } from "constants/defaultMap"
import { worldAngle } from "constants/world"

// Default z-axis scaling for blocks
const heightScaling = 0.25;

var counter = 0;

function stateIncludes(state, obj) {
  for (const c of state) {
    if (c.x === obj.x &&
      c.y === obj.y &&
      c.z === obj.z &&
      c.color === obj.color) {
      return true;
    }
  }
  return false;
}

/* Will return the state with the "_new" name attached to the difference between
 * the prev state and the next state */
export const computeDiff = (prev, next) => {
  const difference = next.filter(c => !stateIncludes(prev, c))
  const intersection = next.filter(c => stateIncludes(prev, c))

  return difference.map((c) => (Object.assign({}, c, { names: [...c.names, "_new"] })))
    .concat(intersection)
}

/* Will return true if the two states are equal; false otherwise */
export const computeEquality = (struct1, struct2) => {
  const a = sortBlocks(struct1).filter((b) => b.color !== "Anchor");
  const b = sortBlocks(struct2).filter((b) => b.color !== "Anchor");

  if (a === b) return true;
  if (a == null || b == null) return false;
  if (a.length !== b.length) return false;

  for (let i = 0; i < a.length; ++i) {
    if (a[i].x !== b[i].x ||
      a[i].y !== b[i].y ||
      a[i].z !== b[i].z ||
      a[i].color !== b[i].color ||
      a[i].shape !== b[i].shape) {
      return false;
    }
  }

  return true;
}

class Blocks extends React.Component {
  static propTypes = {
    blocks: React.PropTypes.array,
    path: React.PropTypes.array,
    pointMarkers: React.PropTypes.array,
    roomMarkers: React.PropTypes.array,
    robot: React.PropTypes.object,
    isoConfig: React.PropTypes.object,
    width: React.PropTypes.number,
    height: React.PropTypes.number
  }

  static defaultProps = {
    isoConfig: {},
    blocks: []
  }

  constructor(props) {
    super(props)
    
    /* Default Isomer config */
    const defaultIsoConfig = {
      // TODO : calculate this
      centerPoint: Point(-5, 20, 0),
      rotation: worldAngle,
      scale: 1,

      blockWidthScale: 0.9,
      selectWidthScale: 0.4,
      //groundRadius: worldRadius,
      gridColor: new Color(50, 50, 50),
      canvasWidth: 2 * 825.0,
      canvasHeight: 2 * 600.0,
      originXratio: 0.5,
      originYratio: 0.5,
      numUnits: 30, // default number of cubes from left to right of the canvas
      maxUnits: 200,
      marginCubes: 1, // how far from the border do we keep the cubes, until we reach max zoom
      nil: null
    }

    this.config = { ...defaultIsoConfig, ...props.isoConfig }

    // infer easier to use arguments
    this.config = (p => {
      p.originX = p.canvasWidth * p.originXratio;
      p.originY = p.canvasHeight * p.originYratio;
      p.unitWidth = p.canvasWidth / p.numUnits;
      p.margin = p.unitWidth * p.marginCubes;
      return p;
    })(this.config);

    this.colorMap = cssColors;
    this.colorMap['fake'] = [255, 255, 255];

    this.state = {
      iso: null,
      rotational: -1,
      animationId: null
    }
  }

  componentDidMount() {
    const iso = new Isomer(this.refs.blocksCanvas,
      {
        scale: this.config.unitWidth,
        originX: this.config.originX,
        originY: this.config.originY
      }
    );

    this.setState({ iso: iso })
  }

  shouldComponentUpdate(prevProps, prevState) {
    return !deepEqual(this.props, prevProps) || !deepEqual(prevState, this.state)
  }

  clone(obj) {
    return JSON.parse(JSON.stringify(obj));
  }

  joinWalls(blocks) {
	
    let wc = worldConfig;
    blocks = blocks.filter(b => b.type !== "wall" || (b.x !== wc.xMin
        && b.x !== wc.xMax && b.y !== wc.yMin && b.y !== wc.yMax));
    let xLen = wc.xMax - wc.xMin;
    let yLen = wc.yMax - wc.yMin;
    let border = [
      { x: wc.xMin+1, y: wc.yMin, type: "wall", extend: { x: xLen-2, y: 0 } },
      { x: wc.xMin, y: wc.yMin+1, type: "wall", extend: { x: 0, y: yLen-2 } },
      { x: wc.xMax, y: wc.yMax, type: "wall", extend: { x: -xLen+2, y: 0 } },
      { x: wc.xMax, y: wc.yMax, type: "wall", extend: { x: 0, y: -yLen+2 } },
      { x: wc.xMin, y: wc.yMin, type: "wall" },
      { x: wc.xMin, y: wc.yMax, type: "wall" },
      { x: wc.xMax, y: wc.yMin, type: "wall" },
      { x: wc.xMax, y: wc.yMax, type: "wall" }
    ];
    return blocks.concat(border);
  }

  componentDidUpdate() {
    counter++;
    let blocks = this.props.blocks;
    
    
    if (worldConfig.optimizeBorder)
      blocks = this.joinWalls(blocks);
    window.requestAnimationFrame(() =>
        this.renderEverything(
            blocks.filter((b) => b.type !== "point"),
            this.clone(this.props.robot),
            this.props.path.slice(),
            0,
            this.props.selectionNumber));
  }

  renderEverything(argBlocks, robot, path, robotStep, selectionNumber) {
	  
    if (counter > 1) {
      counter--;
      return;
    }
    // Robot speed factor
    const factor = 5;
    
    let updatedBlocks = updateRobot(argBlocks, robot, robotStep, path, factor);
    if (robotStep === 0) {
      updatedBlocks.slice().forEach((b) => {
        if (b.type === "item")
          resolveZ(b.x, b.y, updatedBlocks);
        else if (b.type === "wall")
          b.z = 0;
        else if (b.type === "robot")
        robot.z = 0;
      });
    }

    
    // TODO Move this to its own function
    let pm = this.props.pointMarkers;
    let rm = this.props.roomMarkers;
    if (!rm) rm = [];
    if (!pm) pm = [];
    for (let i = 0; i < updatedBlocks.length; ++i) {
      if (updatedBlocks[i].type === "roomMarker" || updatedBlocks[i].type === "pointMarker") {
        updatedBlocks.splice(i,1);
        --i;
      }
    }
    for (let i = 0; i < rm.length; ++i) {
      updatedBlocks.push({x:parseInt(rm[i][0],10), y:parseInt(rm[i][1],10), z:-0.01, color: "cyan", type: "roomMarker"});
    }
    for (let i = 0; i < pm.length; ++i) {
      updatedBlocks.push({x:parseInt(pm[i][0],10), y:parseInt(pm[i][1],10), z:-0.01, color: "fuchsia", type: "pointMarker"});
    }
    
    const blocks = sortBlocks(updatedBlocks.map((b) => rotateBlock(b, this.state.rotational)));
    adjustRobot(robot, blocks);
    // This line will "zoom out" when the blocks get large to display
    //const scalars = blocks.map((b) => this.getBlockScale(b));
    const scalars = blocks.map((b) => 1.0);
    const minScalar = Math.max(Math.min(...scalars), this.config.numUnits / this.config.maxUnits);


    this.state.iso.canvas.clear()
    // this.state.iso._calculateTransformation();
    this.renderBlocks(blocks.filter((b) => b.z < -0.5), minScalar)
    this.renderGrid(minScalar)
    this.renderBlocks(blocks.filter((b) => b.z >= -0.5), minScalar)

    removeRobot(blocks);

    if (path && robotStep < path.length * factor) {
      window.requestAnimationFrame(() => this.renderEverything(blocks, robot, path, robotStep + 1));
    } else {
      counter--;
    }
  }

  getBlockScale(b) {
    const {originX, originY, margin, centerPoint, rotation} = this.config;
    const p = this.state.iso._translatePoint(new Point(b.x, b.y, b.z).rotateZ(centerPoint, rotation));
    // scale is the scaling down required so the point appears in canvas
    // it satisfies: scale * (x - originX) + originX \in [0, canvasWidth]
    // I assume origin is in the box
    // margin is a bit tricky, the exactly way requires multiple calls to translate

    const Y0 = originY;
    const X0 = originX;

    let xscale = 1;
    if (p.x < margin)
      xscale = (X0 - margin) / (X0 - p.x);
    if (p.x > this.config.canvasWidth - margin)
      xscale = (this.config.canvasWidth - margin - X0) / (p.x - X0);

    let yscale = 1;
    if (p.y < margin)
      yscale = (Y0 - margin) / (Y0 - p.y);
    if (p.y > this.config.canvasHeight - margin)
      yscale = (this.config.canvasHeight - margin - Y0) / (p.y - Y0);

    return Math.min(xscale, yscale);
  }

  renderGrid(scale) {
    const { /*groundRadius,*/ rotation, groundColor, centerPoint } = this.config;

    for (let x = 0; x <= worldConfig.xMax - worldConfig.xMin + 1; ++x) {


      this.state.iso.add(new Path([
        new Point((x + worldConfig.xMin), (worldConfig.yMin + 0), 0),
        new Point((x + worldConfig.xMin), (worldConfig.yMax + 1), 0),
        new Point((x + worldConfig.xMin), (worldConfig.yMin + 0), 0)
      ])
        .rotateZ(centerPoint, rotation)
        .scale(centerPoint, scale)
        //.translate(gridwidth*offset, gridwidth*offset, 0)
        , groundColor
      );
    }

    for (let y = 0; y <= worldConfig.yMax - worldConfig.yMin + 1; ++y) {
      this.state.iso.add(new Path([
        new Point((worldConfig.xMin),     (y + worldConfig.yMin + 0), 0),
        new Point((worldConfig.xMax + 1), (y + worldConfig.yMin + 0), 0),
        new Point((worldConfig.xMin),     (y + worldConfig.yMin + 0), 0)
      ])
        .rotateZ(centerPoint, rotation)
        .scale(centerPoint, scale)
        //.translate(gridwidth*offset, gridwidth*offset, 0)
        , groundColor
      );
    }
  }

  renderBlocks(blocks, scale = this.config.scale) {
    if (!(blocks instanceof Array)) {
      blocks = [blocks];
    }
    
    for (const block of blocks) {
      // let selectedBlockYes = false;
      let color = null;
      if (block.color)
        color = this.colorMap[block.color.toLowerCase()];
      let blockColor = new Color();
      // TODO Determine if this should be kept
      if (color) {
        let alpha = 0.88;
        if (block.type === "roomMarker" || block.type === "pointMarker")
          alpha = 0.2;
        blockColor = new Color(color[0], color[1], color[2], alpha);
      } else if (block.type === "robot") {
        blockColor = new Color(128, 128, 128, 0.5);
      } else {
        //blockColor = new Color(128, 128, 128, 0.5);
        blockColor = new Color(0, 0, 0, 0.8);
      }


      // Determine what sort of block to construct
      this.state.iso.add(this.makeBlock(block, false, scale), blockColor);
    }
  }

  darken(color) {
    return new Color(this.darkenValue(color.r), this.darkenValue(color.g), this.darkenValue(color.b), color.a);
  }

  darkenValue(value, factor = 0.5) {
    const graystandard = 128;
    return factor * graystandard + (1 - factor) * value;
  }

  //makeBlock(x, y, z, highlighted = false, scale = this.config.scale, type = null) {
  makeBlock(block, highlighted = false, scale = this.config.scale) {
    const { rotation, centerPoint} = this.config
    const cubesize = highlighted ? this.config.selectWidthScale : this.config.blockWidthScale;
    let { x, y, z, type, shape} = block;
    
    const extend = block.extend ? block.extend : {x:0, y:0};
    if (type === "pointMarker" || type === "roomMarker")
      type = "marker";
    else if (type === "carriedItem"){
      type = "item";
      
    }

    let cScale = 1;
    if (type === "path")
      cScale = 0.25;
    else if (type === "item")
      cScale = 0.75;
    else if (type === "marker")
      cScale = 1;

    let zScale = heightScaling;
    if (type === "robot")
      zScale = 1;
    else if (type === "marker")
      zScale = 0.125;
    else if (type === "wall")
      zScale = 0.125;

    const shift = (1 - cubesize*cScale) / 2;
    const zShift = (1 - cubesize) / 2;

    // Items are rendered as cylinders and must be constructed differently 
    if (type === "item" && shape === "circle") {
      return Shape.Cylinder(
        Point (x + cubesize/2,
          y +  cubesize/2,
          z * heightScaling + zShift),
        0.5 * cScale,
        15,//10, // Number of vertices -- 15 makes them appear as round
        cubesize * heightScaling)
      .rotateZ(centerPoint, rotation)
     .scale(centerPoint, scale);
    }
    else if (type ==="item" && shape ==="triangle"){
    	return Shape.Cylinder(
    	        Point (x + cubesize/2,
    	          y +  cubesize/2,
    	          z * heightScaling + zShift),
    	        0.5 * cScale,
    	        3,
    	        cubesize * heightScaling)
    	      .rotateZ(centerPoint, rotation)
    	     .scale(centerPoint, scale);
		
    }
    else if (type ==="item" && shape ==="square"){
    	return Shape.Cylinder(
    	        Point (x + cubesize/2,
    	          y +  cubesize/2,
    	          z * heightScaling + zShift),
    	        0.5 * cScale,
    	        4,
    	        cubesize * heightScaling)
    	      .rotateZ(centerPoint, rotation)
    	     .scale(centerPoint, scale);
		
    }
    else {
      let shape = Shape.Prism;
      let yRotation = 0;
      if (type === "marker") {
        //shape = Shape.Pyramid;
        //yRotation = Math.PI;
      }
      let xSign = (extend.x >= 0) ? 1 : -1;
      let ySign = (extend.y >= 0) ? 1 : -1;
      if (xSign < 0) x += extend.x - 1;
      if (ySign < 0) y += extend.y - 1;
      let objectPoint = Point(x + shift, y + shift, z * heightScaling + zShift);
      return shape(objectPoint ,
        cubesize*cScale + xSign*extend.x,
        cubesize*cScale + ySign*extend.y,
        cubesize*zScale
      )
        .rotateY(objectPoint, yRotation)
        .rotateZ(centerPoint, rotation)
        .scale(centerPoint, scale)
      //.translate(gridWidth*offset, gridWidth*offset, 0);
    }

  }

  render() {
    return (
      <div>
      <canvas id="blocksCanvas" className="Blocks" ref="blocksCanvas" width={this.props.width} height={this.props.height} />
      </div>
    )
  }
}

export default Blocks
