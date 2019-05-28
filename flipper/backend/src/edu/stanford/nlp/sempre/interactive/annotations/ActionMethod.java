package edu.stanford.nlp.sempre.interactive.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

/**
 * This annotation is currently unused. Hypothetically, this annotation could
 * be used in World and RoboWorld to mark methods that are invoked from the
 * .grammar files. This would make it easier to enforce these methods having
 * a certain return type. (e.g., action methods returning a boolean)
 * @author brendonboldt
 */
@Target(ElementType.METHOD)
public @interface ActionMethod {

}
