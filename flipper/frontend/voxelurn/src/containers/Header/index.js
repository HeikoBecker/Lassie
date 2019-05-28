import React, { PropTypes } from "react"
import {IMPRINT, DATA_PROTECTION} from "constants/strings"
import { Link } from "react-router"
import { connect } from "react-redux"
//import Actions from "actions/world"

import "./styles.css"

const Header = ({ query, signedIn, sessionId, email, dispatch }) => (
  <div className="Header">
    <div className="Header-logo">
      <span>Flipper</span>
      <span className="Header-sublogo">talk to your robot</span>
      <span className="Header-subsublogo"> <a href={IMPRINT}>[Imprint]</a> </span>
      <span className="Header-subsublogo"> <a href={DATA_PROTECTION}>[Data protection]</a> </span>
    </div>
    <div className="Header-nav">
      <Link to={{ pathname: "/about", query: query }} activeClassName="active"><div>About</div></Link>
      <Link to={{ pathname: "/build", query: query }} activeClassName="active"><div>Play</div></Link>
      <Link to={{ pathname: "/tutorial", query: query }} activeClassName="active"><div>Tutorial</div></Link>
      <Link to={{ pathname: "/reference", query: query }} activeClassName="active"><div>Reference</div></Link>
      <Link to={{ pathname: "/syntaxsemantics", query: query }} activeClassName="active"><div>Syntax and Semantics</div></Link>
      <Link to={{ pathname: "/tasks", query: query }} activeClassName="active"><div>Tasks</div></Link>
  {/*
      <Link to={{ pathname: "/community", query: query }} activeClassName="active"><div>Leaderboard</div></Link>
      <a target="_blank" href="https://github.com/sidaw/shrdlurn/blob/master/Voxelurn.md#core-language"><div>Reference</div></a>
      <Link to={{ pathname: "/about", query: query }} activeClassName="active"><div>Help</div></Link>
      {signedIn &&
        <a onClick={() => dispatch(Actions.clear())}><div>Sign Out</div></a>
      }
      {signedIn ?
        <div>
          {email}
        </div>
        :
        <a className="Header-login" href={SLACK_OAUTH_URL}>
          <div>
            <img alt="Click to sign in with Slack" src="https://api.slack.com/img/sign_in_with_slack.png" />
          </div>
        </a>
      }
  */}
    </div>
  </div>
)

Header.propTypes = {
  /* URL parameters in order to persist the query (e.g ?turkid=AMT_123) across
   * route changes */
  query: PropTypes.object
}

const mapStateToProps = (state) => ({
  sessionId: state.user.sessionId,
  email: state.user.email,
  signedIn: state.user.signedIn
})

export default connect(mapStateToProps)(Header)
