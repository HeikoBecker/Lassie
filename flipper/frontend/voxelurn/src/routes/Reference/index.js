import React, { Component } from "react"
import { connect } from "react-redux"
import { Link } from "react-router"
import "./styles.css"
import {} from "constants/strings"
import marked from "marked"

class Reference extends Component {
  constructor() {
    super();
    this.state = { markdown: "Loading..." };
  }

  componentWillMount() {
    const readmePath = require("./reference.md");

    fetch(readmePath)
      .then(response => {
        return response.text()
      })
      .then(text => {
        this.setState({
          markdown: marked(text)
        })
      })
  }


  /* JSX Link example
   * <Link to={{ pathname: "/community", query: this.props.query }} activeClassName="active" target="_blank">voxel structures</Link>.{' '}
   */
	render() {
		const height = "150px";
		return (
			<div className="Reference">
				<div dangerouslySetInnerHTML={{__html: this.state.markdown}} />
      </div>
		)
	}
}

export default connect()(Reference)
