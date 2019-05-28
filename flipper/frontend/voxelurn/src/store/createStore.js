import { applyMiddleware, compose, createStore } from 'redux'
import thunk from 'redux-thunk'
import { persistStore, autoRehydrate } from 'redux-persist'
import makeRootReducer from '.'
import { setStore/*, getStore, genUid*/ } from "helpers/util"

export default (initialState = {}) => {
  /* Build the thunk middleware to enable async redux actions */
  const middleware = [thunk]

  /* Enhance the store with the autoRehydrate enhancer to support redux-persist */
  const enhancers = [autoRehydrate()]

  /* If we are in developer mode, let's load the dev tools enhancement */
  if (process.env.NODE_ENV === 'development') {
    const devToolsExtension = window.devToolsExtension
    if (typeof devToolsExtension === 'function') {
      enhancers.push(devToolsExtension())
    }
  }

  /* Now, create the store */
  const store = createStore(
    makeRootReducer(),
    initialState,
    compose(
      applyMiddleware(...middleware),
      ...enhancers
    )
  )

  let sessionId = Math.random(new Date()/1).toString(36).substr(2,10);
  setStore("uid", sessionId);

  /* Persist the world reducer so that a user's progress can be saved despite
   * reloads (stores this information to localStorage on each update) */
  //persistStore(store, { whitelist: ['world', 'user'] }, () => {
  persistStore(store, { whitelist: ['world'] }, () => {
    console.log("User ID: " + sessionId);
  });

  /* return our created store for future use */
  return store
}
