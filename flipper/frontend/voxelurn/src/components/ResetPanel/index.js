import React, { Component } from "react"
import classnames from "classnames"
import { connect } from "react-redux"
import Actions from "actions/logger"
import WorldActions from "actions/world"

import "./styles.css"

class SharePanel extends Component {
  constructor(props) {
    super(props)
  }



  clear() {
    this.props.dispatch(WorldActions.clear())
  }


  render() {
    return (
      <div className="SidePanel">
        <div className="SidePanel-content">
            <div className="SharePanel-buttons">
                <div className="yourstructs">
                  <table>
                    <tbody>
                    <tr>
                      <td className="Explanation">Reset world to initial state. <br /> (Learned commands are remembered)</td>
                      <td><button id="controlPanel-clear" onClick={() => this.clear()}>Reset</button></td>
                    </tr>
                    </tbody>
                  </table>
                </div>
            </div>
        </div>
      </div>
    )

  }
}

const mapStateToProps = (state) => ({
  user_structs: state.logger.user_structs,
  sessionId: state.user.sessionId,
  sid: state.logger.sid,
  signedIn: state.user.signedIn
})

export default connect(mapStateToProps)(SharePanel)
