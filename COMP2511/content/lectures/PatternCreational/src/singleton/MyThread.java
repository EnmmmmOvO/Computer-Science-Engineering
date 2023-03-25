package singleton;

class MyThread extends Thread {  
    private String name;

    MyThread(String name){  
        this.name = name;
    }  
    
    public void run(){  
        MySingleton2 s1 = MySingleton2.getInstance(); 
    }  
}