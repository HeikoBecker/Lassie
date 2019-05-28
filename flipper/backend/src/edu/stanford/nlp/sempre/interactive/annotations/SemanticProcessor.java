package edu.stanford.nlp.sempre.interactive.annotations;

import java.util.Set;

import javax.annotation.processing.AbstractProcessor;
import javax.annotation.processing.RoundEnvironment;
import javax.lang.model.element.Element;
import javax.lang.model.element.TypeElement;
import javax.tools.Diagnostic;

/**
 * This processor would enforce annotations like `MethodProcessor`
 * Not currently implemented or used
 */
public class SemanticProcessor extends AbstractProcessor {

  @Override
  public boolean process(Set<? extends TypeElement> annotations, RoundEnvironment roundEnv) {

    for (Element elem : roundEnv.getElementsAnnotatedWith(ActionMethod.class)) {
      String message = elem.getSimpleName().toString();
      this.processingEnv.getMessager().printMessage(Diagnostic.Kind.NOTE, message);
    }
    return false;
  }

}
