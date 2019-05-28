import React, { Component } from "react"
import { connect } from "react-redux"
//import Actions from "actions/logger"
import { Link } from "react-router"
import "./styles.css"
import { TUTORIAL_URL, SLACK_SIGNUP_URL, DOCUMENTATION_URL } from "constants/strings"

import MPI_SWS_logo from "images/mpi_sws_logo.png"

class Information extends Component {
	componentDidMount() {
		//this.props.dispatch(Actions.joinCommunity())
	}

  /* JSX Link example
   * <Link to={{ pathname: "/community", query: this.props.query }} activeClassName="active" target="_blank">voxel structures</Link>.{' '}
   */
	render() {
		const height = "50px";
		return (
			<div className="About">
				<div>
					<img src={MPI_SWS_logo} alt="MPI-SWS logo" height={height} />
					<p>Flipper is a natural language  robot interface. If Flipper can not understand your command, 
					you can define it using its <Link to={{pathname: "/syntaxsemantics"}}>core language</Link>. Flipper then learns from your definition, induces 
					new rules for future use (for you and the others) and in some cases generalizes your definition to a more suitable one.</p>
		<h2>Quick start</h2>
		<ul>
			<li> open the <Link to={{pathname: "/build"}}> Play tab</Link> and write a command <b>visit red</b> </li>
			<li> that command is not the part of core language. Unless somebody already naturalized it, Flipper won't know what to do </li>
			<li> write <b>visit world containing item is red</b>. Pres 'try', 'accept' and finally 'finish definition' (as shown in this short <a href="https://youtu.be/Fv7BAqHmNYo">video demo</a>) </li>
			<li> next time you (or somebody else) write <b>visit triangle</b>, Flipper will understand you </li>
            
		</ul>
        <h2>More</h2>
          <ul>
          <li>After finishing <Link to = {{pathname: "/tutorial"}}>the tutorial</Link>, try to solve <Link to={{ pathname: "/tasks" }}>these tasks</Link></li>
          <li> For the details on Flipper, check out <a href="https://arxiv.org/abs/1803.02238">the paper</a></li>
          <li>Check the implementation in <a href="https://github.com/mpi-sws-rse/flipper">this github repository </a></li>
          <li>Flipper is based on the concept of naturalizing a formal language, described in <a href="http://www.voxelurn.com/#/about">Voxelurn building interface</a> </li>
          
          </ul>
        </div></div>
		)
	}
}

const mapStateToProps = (state) => ({
	structs: state.logger.structs,
	utterances: state.logger.utterances,
	topBuilders: state.logger.topBuilders
})

export default connect(mapStateToProps)(Information)
