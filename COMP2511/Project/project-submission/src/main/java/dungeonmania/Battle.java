package dungeonmania;

import dungeonmania.MapGenerator.MapGenerator;

public interface Battle {

    public void battle(MapGenerator mapGenerator, Battle enemy);

    public Double getVita();

    public Double getAttack();

    public void setVita(Double vita);

}
