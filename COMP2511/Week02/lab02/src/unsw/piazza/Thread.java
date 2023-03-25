package unsw.piazza;

import java.util.ArrayList;
import java.util.List;

/**
 * A thread in the Piazza forum.
 */
public class Thread {

    private ArrayList<Post> content;
    private String title;
    private User owner;
    private ArrayList<String> tags;

    /**
     * Creates a new thread with a title and an initial first post.
     * The author of the first post at the time of thread creation is the owner of the thread.
     * The owner cannot change once the thread is created.
     * @param title
     * @param firstPost
     */
    public Thread(String title, Post firstPost) {
        this.title = title;
        content = new ArrayList<>();
        content.add(firstPost);
        this.owner = firstPost.getAuthor();
        tags = new ArrayList<>();
    }

    /**
     * @return The owner of the thread
     */
    public User getOwner() {
        return owner;
    }

    /**
     * @return The title of the thread
     */
    public String getTitle() {
        return title;
    }

    /**
     * @return A SORTED list of unique tags
     */
    public List<String> getTags() {
        return tags;
    }

    /**
     * @return A list of posts in this thread, in the order that they were published
     */
    public List<Post> getPosts() {
        return content;
    }

    /**
     * Adds the given post object into the list of posts in the thread.
     * @param post
     */
    public void publishPost(Post post) {
        content.add(post);
    }

    /**
     * Allows the given user to remove the Post from the thread.
     * Does nothing if the post is not in the thread.
     * @param post
     * @throws PermissionDeniedException if the given user is not an author of the post
     */
    public void removePost(Post post, User by) throws PermissionDeniedException {
        for (int loop = 0; loop < content.size(); loop++) {
            if (post.equals(content.get(loop))) {
                if (!by.equals(content.get(loop).getAuthor()))
                    throw new PermissionDeniedException("Only Content author have permission to remove");
                content.remove(post);
            }
        }
    }

    /**
     * Allows the given uer to edit the thread title.
     * @param title
     * @param by
     * @throws PermissionDeniedException if the given user is not the owner of the thread.
     */
    public void setTitle(String title, User by) throws PermissionDeniedException {
        if (!owner.equals(by)) throw new PermissionDeniedException("Only Thread owner have permission to change the title");
        this.title = title;
    }

    /**
     * Allows the given user to replace the thread tags (list of strings)
     * @param tags
     * @param by
     * @throws PermissionDeniedException if the given user is not the owner of the thread.
     */
    public void setTags(String[] tags, User by) throws PermissionDeniedException {
        if (!owner.equals(by)) throw new PermissionDeniedException("Only Thread owner have permission to change the tags");
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

    /**
     * Search the thread is included the tag or not
     * @param tag
     * @throws if include the tag return true, if no, return false
     */
    public boolean findTags(String tag) {
        for (int loop = 0; loop < tags.size(); loop++)
            if (tags.get(loop).equals(tag)) return true;
        return false;
    }

    /**
     * Search the thread is included the tag or not
     * @param author
     * @throws if include the tag return true, if no, return false
     */
    public List<Post> findAuthorPost(User author) {
        ArrayList<Post> postList = new ArrayList<>();

        for (int loop = 0; loop < content.size(); loop++)
            if (content.get(loop).getAuthor().equals(author)) postList.add(content.get(loop));

        return postList;
    }
}
