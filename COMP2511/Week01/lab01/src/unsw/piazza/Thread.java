package unsw.piazza;

import java.util.ArrayList;
import java.util.List;

/**
 * A thread in the Piazza forum.
 */
public class Thread {

    private ArrayList<String> post;
    private String title;
    private ArrayList<String> tags;

    /**
     * Creates a new thread with a title and an initial first post.
     * @param title
     * @param firstPost
     */
    public Thread(String title, String firstPost) {
        this.title = title;
        tags = new ArrayList<>();
        post = new ArrayList<>();
        post.add(firstPost);
    }

    /**
     * @return The title of the thread
     */
    public String getTitle() {
        return title;
    }

    /**
     * @return A SORTED list of tags
     */
    public List<String> getTags() {
        return tags;
    }

    /**
     * @return A list of posts in this thread, in the order that they were published
     */
    public List<String> getPosts() {
        return post;
    }

    /**
     * Adds the given post object into the list of posts in the thread.
     * @param post
     */
    public void publishPost(String post) {
        this.post.add(post);
    }

    /**
     * Allows the given user to replace the thread tags (list of strings)
     * @param tags
     */
    public void setTags(String[] tags) {
        for (int i = 0; i < tags.length; i++) {
            for (int j = i + 1; j < tags.length; j++) {
                if (tags[i].compareTo(tags[j]) > 0) {
                    String temp = tags[i];
                    tags[i] = tags[j];
                    tags[j] = temp;
                }
            }
        }

        for (int i = 0; i < tags.length; i++) this.tags.add(tags[i]);
    }

    public boolean findTags(String tag) {
        for (int loop = 0; loop < tags.size(); loop++)
            if (tags.get(loop).equals(tag)) return true;
        return false;
    }
}
