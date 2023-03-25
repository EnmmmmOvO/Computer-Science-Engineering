1. We assume when we start a new game, the Inventory list is empty.
 
2. We create a map to store to save games(Map<String, MapGenerator> maps). basically when we call the save game method, we add a new map with its id into   the maps. we will get the map which id equals to the parameter of the method load game from the maps.

3. assume bow and shield is collectable

4. we assume the id for the dungeon is base on the localdatetime

5. we assume the entity id base on the initial position 

6. Sun stone can open all kinds of doors

7. The sceptre buildable condition for treasure/key can't be substituted with sun stone

8. Once the sun stone is used for buildable entities (sceptre/midnightArmour/shield), it can't be retained

9. On each tick map can only have maximum of 4 spiders, and the total number of generated spiders will be 6

10. When zombie is generated after buildableSet containing midnight armour, the midnight armour will be removed from buildableSet

11. No javadoc on setter, getter, constructor and override methods

12. All enemies' vita (health) and attack are set to 10.0 and player's vita/attack are set to 10000000.0
