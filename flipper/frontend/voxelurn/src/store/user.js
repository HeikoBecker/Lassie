import Constants from "constants/actions"
import { DEFAULT_SESSIONID } from "constants/strings"

const initialState = {
  sessionId: DEFAULT_SESSIONID,
  task: "world",
  email: null,
  signedIn: false,
  token: null
}

export default function reducer(state = initialState, action = {}) {
  switch (action.type) {
    case Constants.SET_SESSION_ID:
      return { ...state, sessionId: action.sessionId }
    case Constants.SET_TASK:
      return { ...state, task: action.task }
    case Constants.SIGN_IN:
      return { ...state, sessionId: action.id, email: action.email, signedIn: true, token: action.token }
    case Constants.CLEAR:
      return { ...initialState, sessionId: state.sessionId };
    default:
      return state
  }
}
