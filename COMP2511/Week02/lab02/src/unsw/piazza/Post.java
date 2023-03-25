package unsw.piazza;

import java.util.ArrayList;

/**
 * A post in the Piazza forum
 */
public class Post {

    private String content;
    private User author;
    private ArrayList<User> voteUserList;
    /**
     * Creates a new post by the author with the given content.
     * @param content
     * @param author
     */
    public Post(String content, User author) {
        this.content = content;
        this.author = author;
        voteUserList = new ArrayList<>();
    }

    /**
     * @return Author of the post
     */
    public User getAuthor() {
        return author;
    }

    /**
     * @return The content of the post
     */
    public String getContent() {
        return content;
    }

    /**
     * @return A non-negative integer representing the total number of upvotes
     */
    public int getUpvotes() {
        return voteUserList.size();
    }

    /**
     *  Called when the given user wants to update the content
     *  @param content
     *  @throws PermissionDeniedException if the given user is not the author
     */
    public void setContent(String content, User by) throws PermissionDeniedException {
        if (!by.equals(author)) throw new PermissionDeniedException("Only Content author have permission to change the content");
        this.content = content;
    }

    /**
     * Called when the given user wants to upvote this post.
     * A user can only perform an upvote once. If they try more than once, nothing happens.
     * Users can upvote their own posts.
     * @param by
     */
    public void upvote(User by) {
        for (int loop = 0; loop < voteUserList.size(); loop++)
            if (by.equals(voteUserList.get(loop))) return;
        voteUserList.add(by);
    }
}