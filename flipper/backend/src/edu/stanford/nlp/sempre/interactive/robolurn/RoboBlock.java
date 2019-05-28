package edu.stanford.nlp.sempre.interactive.robolurn;

import java.util.List;

import edu.stanford.nlp.sempre.Json;
import edu.stanford.nlp.sempre.interactive.Block;

public abstract class RoboBlock extends Block {

  static final String WALL_TYPE = "wall";
  static final String ITEM_TYPE = "item";
  
  @SuppressWarnings("unchecked")
  public static RoboBlock fromJSON(String json) {
    List<Object> props = Json.readValueHard(json, List.class);
    return fromJSONObject(props);
  }

  public static RoboBlock fromJSONObject(List<Object> props) {
    if (WALL_TYPE.equals(props.get(2))) {
      return Wall.fromJSONObject(props);
    } else {
      return Item.fromJSONObject(props);
    }
  }
  
  public abstract Object toJSON();
}
