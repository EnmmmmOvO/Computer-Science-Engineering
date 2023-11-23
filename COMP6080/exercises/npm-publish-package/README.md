## Publish an NPM package

Publishing an `npm` package

`npm` is the default package manager for `node.js`, and it has a command line interface that allows a user to easily build all the required libraries for a particular JavaScript (or TypeScript!) project.

To publish an `npm` package, you must first ensure that `node` and `npm` are installed on your system. Then, you must create an `npm` account [here](https://www.npmjs.com/signup).

Afterwards, login through your terminal with 
```sh
npm login
```
and enter all the required details.

___

Create a new folder, which will contain the files that will consist your package. Let's name it `webfeprog-publish-` + today's date. Afterwards, navigate to the newly created folder.

e.g.
```sh
mkdir webfeprog-publish-20jan
cd webfeprog-publish-20jan
```

___

`npm` has certain commands that make it really easy for us to create and publish `npm` packages.

In your terminal, type:
```sh
npm init
```

Afterwards, go through all the prompts as appropriate. This will create a `package.json` file in the root directory of your package.

This `package.json` file will contain all the relevant metadata for your project. You are able to edit these manually through your IDE!

What information do the following fields hold?

- `version`
- `main`
- `scripts`
- `dependencies`
- `repository`
- `author` and `contributors`

___

Let's create an `index.js` file in the root directory for your package, and let's just make it print `Hello world!` to the console.

Now, let's adjust `package.json`. Change the `version` field to `"version": "0.0.1"`, and add yourself to the `author` field.

Finally, let's add a script to the `scripts` field that would run our `index.js`.

Check that it works by running `npm start` in your terminal. It should just say `Hello world!` in your terminal!

___

After all that it's time to publish. To do that, all you need to run is 

```sh
npm publish
```

Seeing your package name and version at the end of `npm publish` means that it worked! For example, I would see 
```sh
+ webfeprog-publish-20jan@0.0.1
```
and I can find the package at [this link](https://www.npmjs.com/package/webfeprog-publish-20jan) afterwards.