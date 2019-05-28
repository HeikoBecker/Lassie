/* Dictionary: implements a list of induced definitions for the user to review them
 * DictionaryItem: a single element of the Dictionary list
 */

import React, { Component, PropTypes } from "react"
import classnames from "classnames"
import Actions from "actions/world"
import { connect } from "react-redux"


import "./styles.css"

class DictionaryPanel extends Component {
	static propTypes = {
	    dispatch: PropTypes.func,
	    dictionary: PropTypes.array
	 }

	 constructor(props) {
		super(props)
		this.reload = this.reload.bind(this)
		this.deleteRule=this.deleteRule.bind(this)
		this.state = ({
			collapsed: true
		})
	}

	/* force update when an induced rule is added or removed
	 * when the dictionary is opened or closed
	 * or when the reload button is clicked*/
	shouldComponentUpdate(nextProps, nextState){
		if (this.props.dictionary.length !== nextProps.dictionary.length ||
			this.state.collapsed !== nextState.collapsed){
			return true
		}
		//Defined a rule (to catch changes not caught by the change in dictionary length)
		else if(this.props.defining !== nextProps.defining) {
			console.log("defined")
	
			return true
		}
		else{
			return false
		}
	}
	
	//force rerendering by changing the state
	reload() {
		  this.props.dispatch(Actions.dictionary())
	}

	
	//Dispatches the action to delete the rule
	deleteRule(index){
		console.log("Delete request " + index)
		this.props.dispatch(Actions.deleteRule(index))
		this.props.dispatch(Actions.dictionary())
	}


	render() {
		return (
			<div className={classnames("Dictionary", {"collapsed": this.state.collapsed})}>
				<div className="Dictionary-header">
				  <div id="dictionaryReload" onClick={this.reload}>
				  	 &#x21BA;
				  </div>
		          <span className="Dictionary-header-name">Dictionary</span>
		          <div onClick={() => 
		          	this.setState({ collapsed: !this.state.collapsed })}
		          	className="Dictionary-header-arrow">
		            {(() => {
		              if (this.state.collapsed) {
		            	  return (<span>&larr;</span>)
		              }
		              else {
		          		  this.props.dispatch(Actions.dictionary())
		            	  return (<span>&rarr;</span>)
		              }
		            })()}
		          </div>
		        </div>
				{!this.state.collapsed && <Dictionary   delete={this.deleteRule}
														sessionId={this.props.sessionId}
														dictionary={this.props.dictionary}/>}
			</div>
		)
	}
}

class Dictionary extends Component{
	static PropTypes= {
		dictionary: PropTypes.array
	}
	
	constructor(props) {
		super(props)
		const length = this.props.dictionary.length;
		this.state={
			clicked: Array(length).fill(false), 
			prevClick: -1
		}
	}
	

	shouldComponentUpdate(nextProps, nextState){
		//dictionary changed
		if (this.props.dictionary.length !== nextProps.dictionary.length) {
			return true
		}
		//a cell has been clicked
		else if (this.state.prevClick !== nextState.prevClick) {
			return true
		}
		else{
			return false
		}
	}

	/** 
	 * Function to allow the clicking of a rule to expand the head and body used to induce it
	*/
	handleClick(i){
		const clicked = this.state.clicked.slice()
		let prevClick = this.state.prevClick
		//there is an element that is already expanded
		if (prevClick >= 0) {
			//expanded cell has been clicked, so we need to reset the cell
			if (prevClick === i) {
				clicked[prevClick] = false
				prevClick = -1
			} 
			//a different cell has been clicked, so expand that cell and reset the first one
			else {
				clicked[prevClick] = false
				clicked[i] = true
				prevClick = i
			}
		}
		//no element is expanded
		else {
			clicked[i] = true
			prevClick = i
		}
		this.setState({
			clicked: clicked,
			prevClick: prevClick
		})
	}
	
	//scroll to top after adding a rule
	componentDidUpdate(prevProps){
		if (this.props.dictionary.length !== prevProps.dictionary.length){
			this.refs.list.scrollTop = 0
			if (this.state.prevClick >= 0) {	
				const clicked = this.state.clicked
				clicked[this.state.prevClick] = false
				this.setState({
					clicked: clicked,
					prevClick: -1
				})
			}
		}
	}
	
	//get array of React elements (tr) to represent the list rules
	getDictionaryCells(){
		const dictionary = this.props.dictionary.slice();
		const arr = dictionary.map((el) => {
			return (
				<DictionaryElement 
						key={el.index} 
						rule={el} 
						clicked={this.state.clicked[el.index]} 
						onClick={() => this.handleClick(el.index)}
						delete={this.props.delete}
						sessionId={this.props.sessionId}/>
			)
		}) 
		return arr
	} 

	render(){
		return (
				<div className="Dictionary-content" ref="list">
		        	<table>
		        		<tbody>
			        	<tr className="Explanation">
			        		<td colSpan="3">Click on a rule to see an example<br />
			        						Click the cross to delete a rule you defined</td>
			        	</tr>
		        			{this.getDictionaryCells()}
		        		</tbody>
		        	</table>
				</div>
		)
	}
}

/** 
 * Functional react component to represent a rule
 * A dictionary element can be clicked to show the head and body used to induce the rule originally.
 * If the user who defined a rule clicks on the rule, they are shown a button to delete the rule.
*/
function DictionaryElement(props) {
		const rule = props.rule
		return (
			<tr className="DictionaryElement"
				onClick={props.onClick}>
			{(() => 
			{if (props.clicked) {
				if (props.sessionId == rule.uid){
					return ([
				         <td className="deleteButton" colSpan="1" key="button">
							<button onClick={() => {props.delete(rule.index)}}> X </button>
						</td>,
						<td className="headButton" colSpan="1" key="head">{rule.head}</td>,
						<td className="body" colSpan="1" key="body">{rule.body}</td>
					])} 
				else {
					return ([
						<td className="headWithoutButton" colSpan="2" key="head">{rule.head}</td>,
						<td className="body" colSpan="1" key="body">{rule.body}</td>
					])} 
			} else {
				return (
					<td colSpan="3">{rule.rhs}</td>
				)}
			})()}
			</tr>)
}

const mapStateToProps = (state) => ({
  dictionary: state.world.dictionary,
  sessionId: state.user.sessionId,
  defining: state.world.defining
})

export default connect(mapStateToProps)(DictionaryPanel)