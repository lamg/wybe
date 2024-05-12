# Develop VSCode plugin

Initialize extension

```sh
sudo snap install node --classic # v20.13.1
mkdir ~/.npm-global
npm config set prefix '~/.npm-global'
npm install -g yo generator-code
yo code
```

- Select `New Language Support`

Use extension:
- execute the VSCode command `Developer: Install extension from location` and choose this directory